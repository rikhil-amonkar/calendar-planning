def get_duration(city_idx):
    return (
        z3.If(city_idx == 0, 4,
              z3.If(city_idx == 1, 4,
                    z3.If(city_idx == 2, 4,
                          z3.If(city_idx == 3, 3,
                                z3.If(city_idx == 4, 3,
                                      z3.If(city_idx == 5, 3, 2)))))))
    )