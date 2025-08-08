# Constraints for date ranges
    for city, (start, end) in constraints:
        city_id = city_ids[city]
        # All days in this city must be within the start-end range
        for i in range(30):
            solver.add(If(days[i] == city_id, And(i+1 >= start, i+1 <= end), True))