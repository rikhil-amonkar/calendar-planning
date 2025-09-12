return z3.If(city_code_var == 0, 2,
             z3.If(city_code_var == 1, 3,
                   z3.If(city_code_var == 2, 3,
                         z3.If(city_code_var == 3, 4,
                               z3.If(city_code_var == 4, 5,
                                     z3.If(city_code_var == 5, 5, 2))))))