set(LUSTREC_ROOT "" CACHE PATH "Root of LUSTREC distribution.")

mark_as_advanced(LUSTREC_EXECUTABLE)
find_program (LUSTREC_EXECUTABLE
  NAMES lustrec PATHS ${LUSTREC_ROOT} PATH_SUFFIXES bin 
  DOC "lustrec command line executable")
mark_as_advanced(LUSTREC_EXECUTABLE)

include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(LUSTREC
  REQUIRED_VARS LUSTREC_EXECUTABLE)
