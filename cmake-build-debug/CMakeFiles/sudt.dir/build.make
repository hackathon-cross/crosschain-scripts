# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.16

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /Applications/CLion.app/Contents/bin/cmake/mac/bin/cmake

# The command to remove a file.
RM = /Applications/CLion.app/Contents/bin/cmake/mac/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /Users/hyz/CLionProjects/crosschain-scripts

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /Users/hyz/CLionProjects/crosschain-scripts/cmake-build-debug

# Include any dependencies generated for this target.
include CMakeFiles/sudt.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/sudt.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/sudt.dir/flags.make

CMakeFiles/sudt.dir/c/simple_udt.c.o: CMakeFiles/sudt.dir/flags.make
CMakeFiles/sudt.dir/c/simple_udt.c.o: ../c/simple_udt.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/hyz/CLionProjects/crosschain-scripts/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object CMakeFiles/sudt.dir/c/simple_udt.c.o"
	/usr/bin/gcc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/sudt.dir/c/simple_udt.c.o   -c /Users/hyz/CLionProjects/crosschain-scripts/c/simple_udt.c

CMakeFiles/sudt.dir/c/simple_udt.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/sudt.dir/c/simple_udt.c.i"
	/usr/bin/gcc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /Users/hyz/CLionProjects/crosschain-scripts/c/simple_udt.c > CMakeFiles/sudt.dir/c/simple_udt.c.i

CMakeFiles/sudt.dir/c/simple_udt.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/sudt.dir/c/simple_udt.c.s"
	/usr/bin/gcc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /Users/hyz/CLionProjects/crosschain-scripts/c/simple_udt.c -o CMakeFiles/sudt.dir/c/simple_udt.c.s

# Object files for target sudt
sudt_OBJECTS = \
"CMakeFiles/sudt.dir/c/simple_udt.c.o"

# External object files for target sudt
sudt_EXTERNAL_OBJECTS =

sudt: CMakeFiles/sudt.dir/c/simple_udt.c.o
sudt: CMakeFiles/sudt.dir/build.make
sudt: CMakeFiles/sudt.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/Users/hyz/CLionProjects/crosschain-scripts/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking C executable sudt"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/sudt.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/sudt.dir/build: sudt

.PHONY : CMakeFiles/sudt.dir/build

CMakeFiles/sudt.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/sudt.dir/cmake_clean.cmake
.PHONY : CMakeFiles/sudt.dir/clean

CMakeFiles/sudt.dir/depend:
	cd /Users/hyz/CLionProjects/crosschain-scripts/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /Users/hyz/CLionProjects/crosschain-scripts /Users/hyz/CLionProjects/crosschain-scripts /Users/hyz/CLionProjects/crosschain-scripts/cmake-build-debug /Users/hyz/CLionProjects/crosschain-scripts/cmake-build-debug /Users/hyz/CLionProjects/crosschain-scripts/cmake-build-debug/CMakeFiles/sudt.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/sudt.dir/depend

