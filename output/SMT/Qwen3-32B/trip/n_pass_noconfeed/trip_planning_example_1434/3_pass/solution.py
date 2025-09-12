def get_duration(city_idx):
    return If(city_idx == 0, 3,
              If(city_idx == 1, 2,
                 If(city_idx == 2, 2,
                    If(city_idx == 3, 5,
                       If(city_idx == 4, 3,
                          If(city_idx == 5, 4,
                             If(city_idx == 6, 4,
                                If(city_idx == 7, 2,
                                   If(city_idx == 8, 2,
                                      If(city_idx == 9, 5, 0)
                                     )
                                  )
                               )
                            )
                         )
                      )
                   )
                )
             )
          )
       )
     )