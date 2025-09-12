def get_duration(city_code):
    return z3.If(city_code == 0, 3,
        z3.If(city_code == 1, 5,
        z3.If(city_code == 2, 2,
        z3.If(city_code == 3, 5,
        z3.If(city_code == 4, 5,
        z3.If(city_code == 5, 5,
        z3.If(city_code == 6, 2,
        z3.If(city_code == 7, 5,
        z3.If(city_code == 8, 4,
        z3.If(city_code == 9, 5, 0)))))))))