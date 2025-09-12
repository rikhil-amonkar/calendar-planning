travel_time = z3.If(prev_loc == 0,  # Richmond
                    z3.If(friend_loc == 0, 0,
                          z3.If(friend_loc == 1, 11,
                                z3.If(friend_loc == 2, 10,
                                      z3.If(friend_loc == 3, 20,
                                            z3.If(friend_loc == 4, 9, 0)))),
                    z3.If(prev_loc == 1,  # Sunset
                          z3.If(friend_loc == 0, 12,
                                z3.If(friend_loc == 1, 0,
                                      z3.If(friend_loc == 2, 15,
                                            z3.If(friend_loc == 3, 24,
                                                  z3.If(friend_loc == 4, 11, 0)))),
                          z3.If(prev_loc == 2,  # Haight
                                z3.If(friend_loc == 0, 10,
                                      z3.If(friend_loc == 1, 15,
                                            z3.If(friend_loc == 2, 0,
                                                  z3.If(friend_loc == 3, 11,
                                                        z3.If(friend_loc == 4, 7, 0)))),
                                z3.If(prev_loc == 3,  # Mission
                                      z3.If(friend_loc == 0, 20,
                                            z3.If(friend_loc == 1, 24,
                                                  z3.If(friend_loc == 2, 12,
                                                        z3.If(friend_loc == 3, 0,
                                                              z3.If(friend_loc == 4, 17, 0)))),
                                      z3.If(prev_loc == 4,  # Golden Gate
                                            z3.If(friend_loc == 0, 7,
                                                  z3.If(friend_loc == 1, 10,
                                                        z3.If(friend_loc == 2, 7,
                                                              z3.If(friend_loc == 3, 17,
                                                                    z3.If(friend_loc == 4, 0, 0)))),
                                            0))))))