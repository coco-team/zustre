set(LUSTREC_ROOT "" CACHE PATH "Root of LUSTREC distribution.")
find_path(LUSTREC_INCLUDE_DIR NAMES math.lusic math.h PATHS ${LUSTREC_ROOT}/include/lustrec/ NO_DEFAULT_PATH)

mark_as_advanced(LUSTREC_EXECUTABLE LUSTREC_INCLUDE_DIR)
find_program (LUSTREC_EXECUTABLE
  NAMES lustrec PATHS ${LUSTREC_ROOT}/bin PATH_SUFFIXES bin
  DOC "lustrec command line executable")
mark_as_advanced(LUSTREC_EXECUTABLE)

include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(LUSTREC
  REQUIRED_VARS LUSTREC_EXECUTABLE LUSTREC_INCLUDE_DIR)
