# based on http://bloerg.net/2012/11/10/cmake-and-distutils.html

find_program(PYTHON "python")

set (SRC
  LogManager.py
  kind2.py
  pick_inv.py
  zustre.py
  Cex.py
  cocoprinter.py
  lustreAnnotation.py
  stats.py
  CoCoSpec.py
  lustreParser.py
  z3_utils.py
  )


option (USE_PY_SETUP "Use python distutils to install python modules" OFF)

if (PYTHON AND NOT USE_PY_SETUP)
  install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} DESTINATION lib/zustrepy
    FILES_MATCHING PATTERN "*.py")
  install (PROGRAMS zustrepy DESTINATION bin RENAME zustre)
endif()

if (PYTHON AND USE_PY_SETUP)
  set(SETUP_PY_IN "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in")
  set(SETUP_PY    "${CMAKE_CURRENT_BINARY_DIR}/setup.py")
  set(OUTPUT      "${CMAKE_CURRENT_BINARY_DIR}/build/timestamp")

  set(DEPS  ${SRC}
    ${SETUP_PY_IN}
    )

  configure_file(${SETUP_PY_IN} ${SETUP_PY})

  add_custom_command(OUTPUT ${OUTPUT}
    COMMAND ${PYTHON} ${SETUP_PY} build
    COMMAND ${CMAKE_COMMAND} -E touch ${OUTPUT}
    DEPENDS ${DEPS})

  add_custom_target(python ALL DEPENDS ${OUTPUT})

  install(CODE "execute_process(COMMAND ${PYTHON} ${SETUP_PY} install --install-lib ${CMAKE_INSTALL_PREFIX}/bin --install-scripts ${CMAKE_INSTALL_PREFIX}/bin)")
endif()
