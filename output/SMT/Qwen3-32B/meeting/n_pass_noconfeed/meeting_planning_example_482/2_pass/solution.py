# Compute travel time for this step
travel_time_step = If(
    prev_loc == 0,
    If(current_loc == 0, 0,
        If(current_loc == 1, 11,
            If(current_loc == 2, 18,
                If(current_loc == 3, 12,
                    If(current_loc == 4, 17,
                        If(current_loc == 5, 23, 0)
                    )
                )
            )
        )
    ),
    If(
        prev_loc == 1,
        If(current_loc == 0, 12,
            If(current_loc == 1, 0,
                If(current_loc == 2, 15,
                    If(current_loc == 3, 16,
                        If(current_loc == 4, 15,
                            If(current_loc == 5, 22, 0)
                        )
                    )
                )
            )
        ),
        If(
            prev_loc == 2,
            If(current_loc == 0, 19,
                If(current_loc == 1, 13,
                    If(current_loc == 2, 0,
                        If(current_loc == 3, 23,
                            If(current_loc == 4, 23,
                                If(current_loc == 5, 25, 0)
                            )
                        )
                    )
                )
            ),
            If(
                prev_loc == 3,
                If(current_loc == 0, 11,
                    If(current_loc == 1, 15,
                        If(current_loc == 2, 22,
                            If(current_loc == 3, 0,
                                If(current_loc == 4, 7,
                                    If(current_loc == 5, 13, 0)
                                )
                            )
                        )
                    )
                ),
                If(
                    prev_loc == 4,
                    If(current_loc == 0, 17,
                        If(current_loc == 1, 16,
                            If(current_loc == 2, 23,
                                If(current_loc == 3, 7,
                                    If(current_loc == 4, 0,
                                        If(current_loc == 5, 7, 0)
                                    )
                                )
                            )
                        )
                    ),
                    If(
                        prev_loc == 5,
                        If(current_loc == 0, 22,
                            If(current_loc == 1, 22,
                                If(current_loc == 2, 26,
                                    If(current_loc == 3, 12,
                                        If(current_loc == 4, 7,
                                            If(current_loc == 5, 0, 0)
                                        )
                                    )
                                )
                            )
                        ),
                        0
                    )
                )
            )
        )
    )
)