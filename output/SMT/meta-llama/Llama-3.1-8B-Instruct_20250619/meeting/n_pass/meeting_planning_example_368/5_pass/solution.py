total_travel_time_expr = 0
for friend in friends:
    for location in locations:
        for other_location in locations:
            if location!= other_location:
                total_travel_time_expr += travel_times[location][other_location]
s.maximize(total_travel_time_expr.as_expr())