travel_time_expr = 19 if (current_loc == 1) else (
    16 if (current_loc == 2) else (
        8 if (current_loc == 3) else (
            24 if (current_loc == 4) else (
                11 if (current_loc == 5) else 0
            )
        )
    )
)