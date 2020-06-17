#include "blockchain.h"
#include "blake2b.h"
#include "ckb_syscalls.h"
#include "common.h"
#include "protocol.h"
#include "secp256k1_helper.h"


#define BLAKE2B_BLOCK_SIZE 32
#define SCRIPT_SIZE 32768

#define ERROR_ARGUMENTS_LEN -1
#define ERROR_ENCODING -2
#define ERROR_SYSCALL -3
#define ERROR_SCRIPT_TOO_LONG -21
#define ERROR_OVERFLOWING -51
#define ERROR_1ST_CELL_TYPE_HASH_NOT_MATCH -52
#define ERROR_LOAD_INPUT -53

// Common definitions here, one important limitation, is that this lock script only works
// with scripts and witnesses that are no larger than 32KB. We believe this should be enough
// for most cases.
//
// Here we are also employing a common convention: we append the recovery ID to the end of
// the 64-byte compact recoverable signature.
#define BLAKE2B_BLOCK_SIZE 32
#define BLAKE160_SIZE 20
#define PUBKEY_SIZE 33
#define TEMP_SIZE 32768
#define RECID_INDEX 64
/* 32 KB */
#define MAX_WITNESS_SIZE 32768
#define SCRIPT_SIZE 32768
#define SIGNATURE_SIZE 65

// Compile-time guard against buffer abuse
#if (MAX_WITNESS_SIZE > TEMP_SIZE) || (SCRIPT_SIZE > TEMP_SIZE)
#error "Temp buffer is not big enough!"
#endif



#define ERROR_GROUP_OUTPUT_INVALID -100
#define ERROR_GROUP_INPUT_INVALID -101
#define ERROR_CAPACITY_INVALID -102
#define ERROR_VALIDATOR_SIGNATURE_INVALID -103

typedef unsigned __int128 uint128_t;

int verify_init();
int verify_transfer();
int load_witness_pubkey_hash(unsigned char temp[TEMP_SIZE]);


int get_cell_num(size_t cell_type ) {
    int ret;
    int i = 0;
    uint8_t buffer[1];
    uint64_t len = 1;

    while (1) {
        ret = ckb_load_cell_data(buffer, &len, 0, i,
                                 cell_type);
        if (ret == CKB_INDEX_OUT_OF_BOUND) {
            break;
        }
        i += 1;
    }
    return i;
}

int main() {
    unsigned char script[SCRIPT_SIZE];
    uint64_t len = SCRIPT_SIZE;

    // get myself script
    int ret = ckb_load_script(script, &len, 0);
    if (ret != CKB_SUCCESS) {
        return ERROR_SYSCALL;
    }
    if (len > SCRIPT_SIZE) {
        return ERROR_SCRIPT_TOO_LONG;
    }

    int input_group_num = get_cell_num(CKB_SOURCE_GROUP_INPUT);
    int output_group_num = get_cell_num(CKB_SOURCE_GROUP_OUTPUT);
    if (output_group_num != 1) {
        return ERROR_GROUP_OUTPUT_INVALID;
    }
    if (input_group_num != 0 && input_group_num != 1 ) {
        return ERROR_GROUP_INPUT_INVALID;
    }

    // init type
    if  (input_group_num == 0) {
        return verify_init();
    }

    // transfer type
    return verify_transfer(script);
}

int verify_transfer(unsigned char *script) {
    /*
     * First, ensures that the input capacity less than output capacity in typescript groups
     * for the input and output cells.
     */
    uint64_t input_capacity = 0, output_capacity = 0;
    int len = 8;
    int ret = ckb_load_cell_by_field((uint8_t*) &input_capacity, &len, 0, 0,
                                 CKB_SOURCE_GROUP_INPUT, CKB_CELL_FIELD_CAPACITY);
    if (ret != CKB_SUCCESS) {
        return ret;
    }

    len = 8;
    ret = ckb_load_cell_by_field((uint8_t*) &output_capacity, &len, 0, 0,
                                 CKB_SOURCE_GROUP_OUTPUT, CKB_CELL_FIELD_CAPACITY);
    if (ret != CKB_SUCCESS) {
        return ret;
    }

    if (input_capacity > output_capacity) {
        return ERROR_CAPACITY_INVALID;
    }

    /*
     * Second, verify sig of validator
     *  1. Load sig from output witness
     *  2. Verify sig, ensure it is one of validators from init args
     */
    unsigned char temp[TEMP_SIZE];
    unsigned char lock_bytes[SIGNATURE_SIZE];

    // First let's load and extract script args part, which is also the blake160 hash of public
    // key from current running script.
    len = SCRIPT_SIZE;
    ret = ckb_load_script(script, &len, 0);
    if (ret != CKB_SUCCESS) {
        return ERROR_SYSCALL;
    }
    if (len > SCRIPT_SIZE) {
        return ERROR_SCRIPT_TOO_LONG;
    }
    mol_seg_t script_seg;
    script_seg.ptr = (uint8_t *)script;
    script_seg.size = len;

    if (MolReader_Script_verify(&script_seg, false) != MOL_OK) {
        return ERROR_ENCODING;
    }

    mol_seg_t args_seg = MolReader_Script_get_args(&script_seg);
    mol_seg_t args_bytes_seg = MolReader_Bytes_raw_bytes(&args_seg);
    // args is bytes combine pubkey hashes of validators, not include length
    if (args_bytes_seg.size % BLAKE160_SIZE != 0) {
        return ERROR_ARGUMENTS_LEN;
    }

    // Load the first witness, or the witness of the same index as the first input using
    // current script.
    uint64_t witness_len = MAX_WITNESS_SIZE;
    ret = ckb_load_witness(temp, &witness_len, 0, 0, CKB_SOURCE_GROUP_INPUT);
    if (ret != CKB_SUCCESS) {
        return ERROR_SYSCALL;
    }

    if (witness_len > MAX_WITNESS_SIZE) {
        return ERROR_WITNESS_SIZE;
    }

    // We will treat the first witness as WitnessArgs object, and extract the lock field
    // from the object.
    mol_seg_t lock_bytes_seg;
    ret = extract_witness_lock(temp, witness_len, &lock_bytes_seg);
    if (ret != 0) {
        return ERROR_ENCODING;
    }

    // The lock field must be 65 byte long to represent a (possibly) valid signature.
    if (lock_bytes_seg.size != SIGNATURE_SIZE) {
        return ERROR_ARGUMENTS_LEN;
    }
    // We keep the signature in the temporary location, since later we will modify the
    // WitnessArgs object in place for message hashing.
    memcpy(lock_bytes, lock_bytes_seg.ptr, lock_bytes_seg.size);

    // Load the current transaction hash.
    unsigned char tx_hash[BLAKE2B_BLOCK_SIZE];
    len = BLAKE2B_BLOCK_SIZE;
    ret = ckb_load_tx_hash(tx_hash, &len, 0);
    if (ret != CKB_SUCCESS) {
        return ret;
    }
    if (len != BLAKE2B_BLOCK_SIZE) {
        return ERROR_SYSCALL;
    }

    // Here we start to prepare the message used in signature verification. First, let's
    // hash the just loaded transaction hash.
    unsigned char message[BLAKE2B_BLOCK_SIZE];
    blake2b_state blake2b_ctx;
    blake2b_init(&blake2b_ctx, BLAKE2B_BLOCK_SIZE);
    blake2b_update(&blake2b_ctx, tx_hash, BLAKE2B_BLOCK_SIZE);

    // We've already saved the signature above to a different location. We can then modify
    // the witness object in place to save both memory usage and runtime cycles. The message
    // requires us to use all zeros in the place where a signature should be presented.
    memset((void *)lock_bytes_seg.ptr, 0, lock_bytes_seg.size);
    // Before hashing each witness, we need to hash the witness length first as a 64-bit
    // unsigned little endian integer.
    blake2b_update(&blake2b_ctx, (char *)&witness_len, sizeof(uint64_t));
    // Now let's hash the first modified witness.
    blake2b_update(&blake2b_ctx, temp, witness_len);

    // Let's loop and hash all witnesses with the same indices as the remaining input cells
    // using current running lock script.
    size_t i = 1;
    while (1) {
        len = MAX_WITNESS_SIZE;
        // Using *CKB_SOURCE_GROUP_INPUT* as the source value provides us with a quick way to
        // loop through all input cells using current running lock script. We don't have to
        // loop and check each individual cell by ourselves.
        ret = ckb_load_witness(temp, &len, 0, i, CKB_SOURCE_GROUP_INPUT);
        if (ret == CKB_INDEX_OUT_OF_BOUND) {
            break;
        }
        if (ret != CKB_SUCCESS) {
            return ERROR_SYSCALL;
        }
        if (len > MAX_WITNESS_SIZE) {
            return ERROR_WITNESS_SIZE;
        }
        // Before hashing each witness, we need to hash the witness length first as a 64-bit
        // unsigned little endian integer.
        blake2b_update(&blake2b_ctx, (char *)&len, sizeof(uint64_t));
        blake2b_update(&blake2b_ctx, temp, len);
        i += 1;
    }
    // For safety consideration, this lock script will also hash and guard all witnesses that
    // have index values equal to or larger than the number of input cells. It assumes all
    // witnesses that do have an input cell with the same index, will be guarded by the lock
    // script of the input cell.
    //
    // For convenience reason, we provide a utility function here to calculate the number of
    // input cells in a transaction.
    i = calculate_inputs_len();
    while (1) {
        len = MAX_WITNESS_SIZE;
        // Here we are guarding input cells with any arbitrary lock script, hence we are using
        // the plain *CKB_SOURCE_INPUT* source to loop all witnesses.
        ret = ckb_load_witness(temp, &len, 0, i, CKB_SOURCE_INPUT);
        if (ret == CKB_INDEX_OUT_OF_BOUND) {
            break;
        }
        if (ret != CKB_SUCCESS) {
            return ERROR_SYSCALL;
        }
        if (len > MAX_WITNESS_SIZE) {
            return ERROR_WITNESS_SIZE;
        }
        // Before hashing each witness, we need to hash the witness length first as a 64-bit
        // unsigned little endian integer.
        blake2b_update(&blake2b_ctx, (char *)&len, sizeof(uint64_t));
        blake2b_update(&blake2b_ctx, temp, len);
        i += 1;
    }
    // Now the message preparation is completed.
    blake2b_final(&blake2b_ctx, message, BLAKE2B_BLOCK_SIZE);

    // We are using bitcoin's [secp256k1 library](https://github.com/bitcoin-core/secp256k1)
    // for signature verification here. To the best of our knowledge, this is an unmatched
    // advantage of CKB: you can ship cryptographic algorithm within your smart contract,
    // you don't have to wait for the foundation to ship a new cryptographic algorithm. You
    // can just build and ship your own.
    secp256k1_context context;
    uint8_t secp_data[CKB_SECP256K1_DATA_SIZE];
    ret = ckb_secp256k1_custom_verify_only_initialize(&context, secp_data);
    if (ret != 0) {
        return ret;
    }

    secp256k1_ecdsa_recoverable_signature signature;
    if (secp256k1_ecdsa_recoverable_signature_parse_compact(
            &context, &signature, lock_bytes, lock_bytes[RECID_INDEX]) == 0) {
        return ERROR_SECP_PARSE_SIGNATURE;
    }

    // From the recoverable signature, we can derive the public key used.
    secp256k1_pubkey pubkey;
    if (secp256k1_ecdsa_recover(&context, &pubkey, &signature, message) != 1) {
        return ERROR_SECP_RECOVER_PUBKEY;
    }

    // Let's serialize the signature first, then generate the blake2b hash.
    size_t pubkey_size = PUBKEY_SIZE;
    if (secp256k1_ec_pubkey_serialize(&context, temp, &pubkey_size, &pubkey,
                                      SECP256K1_EC_COMPRESSED) != 1) {
        return ERROR_SECP_SERIALIZE_PUBKEY;
    }

    blake2b_init(&blake2b_ctx, BLAKE2B_BLOCK_SIZE);
    blake2b_update(&blake2b_ctx, temp, pubkey_size);
    blake2b_final(&blake2b_ctx, temp, BLAKE2B_BLOCK_SIZE);

    // As mentioned above, we are only using the first 160 bits(20 bytes), if they match
    // the value provided as the first 20 bytes of script args, the signature verification
    // is considered to be successful.
    int index = 0;
    while (index + BLAKE160_SIZE <= args_bytes_seg.size) {
        if (memcmp(args_bytes_seg.ptr + index, temp, BLAKE160_SIZE) == 0) {
            return CKB_SUCCESS;
        }

        index += BLAKE160_SIZE;
    }


    // Todo: verify sudt amount


    return ERROR_VALIDATOR_SIGNATURE_INVALID;
}

int verify_init() {
    return CKB_SUCCESS;
}
