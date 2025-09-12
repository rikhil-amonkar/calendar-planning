def get_required_duration(city):
    return If(
        city == city_consts_dict["Copenhagen"], 2,
        If(city == city_consts_dict["Geneva"], 3,
           If(city == city_consts_dict["Mykonos"], 1,
              If(city == city_consts_dict["Naples"], 2,
                 If(city == city_consts_dict["Prague"], 1,
                    If(city == city_consts_dict["Dubrovnik"], 1,
                       If(city == city_consts_dict["Athens"], 3,
                          If(city == city_consts_dict["Santorini"], 2,
                             If(city == city_consts_dict["Brussels"], 2, 4)))))))))))