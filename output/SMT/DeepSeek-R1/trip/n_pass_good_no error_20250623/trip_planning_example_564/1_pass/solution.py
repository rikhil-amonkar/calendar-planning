from z3 import *

def main():
    # Define city indices and their required days
    cities = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    days_arr = [2, 3, 4, 7, 4]  # days for Istanbul, Rome, Seville, Naples, Santorini

    # Direct flights (undirected) as tuples of indices
    flights_set = [
        (city_to_index['Rome'], city_to_index['Santorini']),
        (city_to_index['Seville'], city_to_index['Rome']),
        (city_to_index['Istanbul'], city_to_index['Naples']),
        (city_to_index['Naples'], city_to_index['Santorini']),
        (city_to_index['Rome'], city_to_index['Naples']),
        (city_to_index['Rome'], city_to_index['Istanbul'])
    ]

    # Setup Z3 variables
    stay0, stay1, stay2, stay3, stay4 = Ints('stay0 stay1 stay2 stay3 stay4')
    stay_vars = [stay0, stay1, stay2, stay3, stay4]
    s = Solver()

    # Each stay variable must be between 0 and 4 (city indices)
    for var in stay_vars:
        s.add(var >= 0, var < 5)
    s.add(Distinct(stay0, stay1, stay2, stay3, stay4))

    # Function to get days for a city index
    def get_days(city_var):
        return If(city_var == 0, days_arr[0],
                If(city_var == 1, days_arr[1],
                If(city_var == 2, days_arr[2],
                If(city_var == 3, days_arr[3],
                If(city_var == 4, days_arr[4], 0)))))

    # Define start and end days for each stay
    start0 = 1
    end0 = start0 + get_days(stay0) - 1
    start1 = end0
    end1 = start1 + get_days(stay1) - 1
    start2 = end1
    end2 = start2 + get_days(stay2) - 1
    start3 = end2
    end3 = start3 + get_days(stay3) - 1
    start4 = end3
    end4 = start4 + get_days(stay4) - 1
    s.add(end4 == 16)  # Total days must be 16

    # Flight connectivity constraints
    def flight_ok(c1, c2):
        options = []
        for (a, b) in flights_set:
            options.append(And(c1 == a, c2 == b))
            options.append(And(c1 == b, c2 == a))
        return Or(options)

    s.add(flight_ok(stay0, stay1))
    s.add(flight_ok(stay1, stay2))
    s.add(flight_ok(stay2, stay3))
    s.add(flight_ok(stay3, stay4))

    # Istanbul must cover day 6 or 7
    istanbul_cond = False
    for i, (s_var, start, end) in enumerate(zip(
        stay_vars, 
        [start0, start1, start2, start3, start4],
        [end0, end1, end2, end3, end4]
    )):
        cond_i = And(s_var == city_to_index['Istanbul'], 
                    Or(And(start <= 6, 6 <= end),
                       And(start <= 7, 7 <= end)))
        istanbul_cond = Or(istanbul_cond, cond_i)
    s.add(istanbul_cond)

    # Santorini must cover at least one day between 13 and 16
    santorini_cond = False
    for i, (s_var, start, end) in enumerate(zip(
        stay_vars, 
        [start0, start1, start2, start3, start4],
        [end0, end1, end2, end3, end4]
    )):
        cond_i = And(s_var == city_to_index['Santorini'], 
                    And(start <= 16, end >= 13))
        santorini_cond = Or(santorini_cond, cond_i)
    s.add(santorini_cond)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        stay0_val = model[stay0].as_long()
        stay1_val = model[stay1].as_long()
        stay2_val = model[stay2].as_long()
        stay3_val = model[stay3].as_long()
        stay4_val = model[stay4].as_long()
        stay_vals = [stay0_val, stay1_val, stay2_val, stay3_val, stay4_val]
        city_sequence = [cities[idx] for idx in stay_vals]

        # Calculate start and end days
        start_days = [1]
        end_days = [1 + days_arr[stay_vals[0]] - 1]
        for i in range(1, 5):
            start_days.append(end_days[i-1])
            end_days.append(start_days[i] + days_arr[stay_vals[i]] - 1)

        # Build itinerary
        itinerary = []
        for i in range(5):
            city = city_sequence[i]
            start = start_days[i]
            end = end_days[i]
            # Add the block for the entire stay
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            # Add the departure day if not the last city
            if i < 4:
                itinerary.append({"day_range": f"Day {end}", "place": city})
                # Add the arrival day for the next city
                next_city = city_sequence[i+1]
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        # For the last city, no departure, but add the block for the entire stay
        # The block for the last city is already added in the loop

        # Output the result
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()