def get_duration(city_var):
    return If(city_var == City.Valencia, 2,
              If(city_var == City.Oslo, 3,
                 If(city_var == City.Lyon, 4,
                    If(city_var == City.Prague, 3,
                       If(city_var == City.Paris, 4,
                          If(city_var == City.Nice, 4,
                             If(city_var == City.Seville, 5,
                                If(city_var == City.Tallinn, 2,
                                   If(city_var == City.Mykonos, 5,
                                      If(city_var == City.Lisbon, 2, 0)))))))))))))  # One extra closing parenthesis added