cmake_minimum_required(VERSION 2.8.11)

project (Zustre)
set (Zustre_VERSION_MAJOR 0)
set (Zustre_VERSION_MINOR 1)
set (Zustre_VERSION_PATCH 0)
set (Zustre_VERSION_TWEAK "rc2")

if (NOT PACKAGE_VERSION)
  set(PACKAGE_VERSION
    "${Zustre_VERSION_MAJOR}.${Zustre_VERSION_MINOR}.${Zustre_VERSION_PATCH}")
  if (DEFINED Zustre_VERSION_TWEAK)
    set (PACKAGE_VERSION "${PACKAGE_VERSION}-${Zustre_VERSION_TWEAK}")
  endif()
  set (Zustre_VERSION_INFO ${PACKAGE_VERSION})
endif()


if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR )
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")
endif()

enable_testing()
include (CTest)

# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

find_package (Git)
if (GIT_FOUND)
  set (LUSTREC_REPO "https://github.com/coco-team/lustrec"
    CACHE STRING "lustrec repo")
  add_custom_target (lustrec-git
    ${GIT_EXECUTABLE} clone ${LUSTREC_REPO} ${CMAKE_SOURCE_DIR}/lustrec)
  add_custom_target (extra DEPENDS lustrec-git)
else()
  message (STATUS "Could not find git. Not adding 'extra' target.")
endif()

include(ExternalProject)
set_property(DIRECTORY PROPERTY EP_STEP_TARGETS configure build test)

set (Z3_TAG "origin/spacer3" CACHE STRING "Z3 git tag to use")
set (Z3_REPO "https://bitbucket.org/spacer/code.git" CACHE STRING "Z3 repo")
if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set (Z3_DEBUG "-d")
else()
  set (Z3_DEBUG "")
endif()

ExternalProject_Add(z3
  GIT_REPOSITORY  ${Z3_REPO}
  GIT_TAG ${Z3_TAG}
  BUILD_IN_SOURCE 1
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CONFIGURE_COMMAND env CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER}
  ./configure -p <INSTALL_DIR> -b build --staticlib ${Z3_DEBUG}
  BUILD_COMMAND make -j3 -C build
  INSTALL_COMMAND make -C build install
  COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_INSTALL 1
  LOG_BUILD 1)

find_package(Z3 4.3.2)
if (NOT Z3_FOUND)
  ExternalProject_Get_Property (z3 INSTALL_DIR)
  set(Z3_ROOT ${INSTALL_DIR} CACHE PATH "Forced location of Z3" FORCE)
  message(WARNING "No Z3 found. Run \n\tcmake --build . && cmake ${CMAKE_SOURCE_DIR}")
else()
  set_target_properties(z3 PROPERTIES EXCLUDE_FROM_ALL ON)
  include_directories(${Z3_INCLUDE_DIR})
  message ("Found Z3 at ${Z3_EXECUTABLE}")
  # indicate that we want z3 binary to be included in the binary distribution
  install (PROGRAMS ${Z3_EXECUTABLE} DESTINATION bin)
endif()


find_package(LUSTREC)
if (NOT LUSTREC_FOUND)
  # ExternalProject_Get_Property (lustrec INSTALL_DIR)
  set(LUSTREC_ROOT ${INSTALL_DIR} CACHE PATH "Forced location of LUSTREC" FORCE)
  message(WARNING "No LUSTREC found. \n\t Set location of lusterc with option  -DLUSTREC_EXECUTABLE=  ")
else()
  # set_target_properties(lustrec PROPERTIES EXCLUDE_FROM_ALL ON)
  message ("Found LUSTREC at ${LUSTREC_EXECUTABLE}")
  # indicate that we want lustrec binary to be included in the binary distribution
  include_directories(${LUSTREC_INCLUDE_DIR})
  install (PROGRAMS ${LUSTREC_EXECUTABLE} DESTINATION bin)
  install (DIRECTORY ${LUSTREC_INCLUDE_DIR} DESTINATION include)
endif()



set (PACKAGE_NAME Zustre)
set(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")

# Configure CPack.
include(TargetArch)
target_architecture(CMAKE_TARGET_ARCH)
message ("arch: ${CMAKE_TARGET_ARCH}")
set(CPACK_PACKAGE_INSTALL_DIRECTORY "Zustre")
set(CPACK_PACKAGE_VENDOR "Zustre")
set(CPACK_PACKAGE_VERSION_MAJOR ${Zustre_VERSION_MAJOR})
set(CPACK_PACKAGE_VERSION_MINOR ${Zustre_VERSION_MINOR})
set(CPACK_PACKAGE_VERSION_PATCH ${Zustre_VERSION_PATCH})
set(CPACK_PACKAGE_VERSION ${PACKAGE_VERSION})
set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_SOURCE_DIR}/LICENSE")
set(CPACK_RESOURCE_FILE_README "${CMAKE_CURRENT_SOURCE_DIR}/README.md")
set(CPACK_PACKAGE_DESCRIPTION_FILE "${CMAKE_CURRENT_SOURCE_DIR}/README.md")
if(CMAKE_BUILD_TYPE STREQUAL Release)
  set(CPACK_PACKAGE_FILE_NAME
    "${CMAKE_PROJECT_NAME}-${CPACK_PACKAGE_VERSION}-${CMAKE_SYSTEM_NAME}-${CMAKE_TARGET_ARCH}")
else()
  set(CPACK_PACKAGE_FILE_NAME
    "${CMAKE_PROJECT_NAME}-${CPACK_PACKAGE_VERSION}-${CMAKE_SYSTEM_NAME}-${CMAKE_TARGET_ARCH}-${CMAKE_BUILD_TYPE}")
endif()
if(WIN32 AND NOT UNIX)
  set(CPACK_NSIS_MODIFY_PATH "ON")
  set(CPACK_NSIS_ENABLE_UNINSTALL_BEFORE_INSTALL "ON")
  set(CPACK_NSIS_EXTRA_INSTALL_COMMANDS
    "ExecWait '$INSTDIR/tools/msbuild/install.bat'")
  set(CPACK_NSIS_EXTRA_UNINSTALL_COMMANDS
    "ExecWait '$INSTDIR/tools/msbuild/uninstall.bat'")
endif()
include(CPack)

install (FILES ${CMAKE_CURRENT_SOURCE_DIR}/README.md DESTINATION .)
# install all the licenses
install (FILES  ${CMAKE_CURRENT_SOURCE_DIR}/LICENSE
  DESTINATION share/
  RENAME zustre_license.txt)

if (EXISTS z3-prefix/src/z3/LICENSE.txt)
  install (
    FILES
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/LICENSE.txt
    DESTINATION share/
    RENAME z3_license.txt)
endif()

if (EXISTS ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build)
  file(GLOB z3py
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.py?
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.py?
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.so
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.dylib
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.dll
    )
  install(FILES ${z3py} DESTINATION lib/z3py)
endif()
add_subdirectory(src)
