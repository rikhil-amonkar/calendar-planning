from z3 import *

def main():
    # Define the city enum
    City = Datatype('City')
    City.declare('Berlin')
    City.declare('Nice')
    City.declare('Athens')
    City.declare('Stockholm')
    City.declare('Barcelona')
    City.declare('Vilnius')
    City.declare('Lyon')
    City = City.create()
    cities = [City.Berlin, City.Nice, City.Athens, City.Stockholm, City.Barcelona, City.Vilnius, City.Lyon]
    city_names = {
        City.Berlin: "Berlin",
        City.Nice: "Nice",
        City.Athens: "Athens",
        City.Stockholm: "Stockholm",
        City.Barcelona: "Barcelona",
        City.Vilnius: "Vilnius",
        City.Lyon: "Lyon"
    }

    # Direct flight connections (as strings)
    connections_str = [
        "Lyon and Nice",
        "Stockholm and Athens",
        "Nice and Athens",
        "Berlin and Athens",
        "Berlin and Nice",
        "Berlin and Barcelona",
        "Berlin and Vilnius",
        "Barcelona and Nice",
        "Athens and Vilnius",
        "Berlin and Stockholm",
        "Nice and Stockholm",
        "Barcelona and Athens",
        "Barcelona and Stockholm",
        "Barcelona and Lyon"
    ]

    # Convert to list of tuples (city constants)
    allowed_pairs = []
    for conn in connections_str:
        parts = conn.split(" and ")
        c1 = parts[0]
        c2 = parts[1]
        # Map string to the City constant
        if c1 == "Berlin": c1_const = City.Berlin
        elif c1 == "Nice": c1_const = City.Nice
        elif c1 == "Athens": c1_const = City.Athens
        elif c1 == "Stockholm": c1_const = City.Stockholm
        elif c1 == "Barcelona": c1_const = City.Barcelona
        elif c1 == "Vilnius": c1_const = City.Vilnius
        elif c1 == "Lyon": c1_const = City.Lyon
        else: raise ValueError(f"Unknown city: {c1}")
        if c2 == "Berlin": c2_const = City.Berlin
        elif c2 == "Nice": c2_const = City.Nice
        elif c2 == "Athens": c2_const = City.Athens
        elif c2 == "Stockholm": c2_const = City.Stockholm
        elif c2 == "Barcelona": c2_const = City.Barcelona
        elif c2 == "Vilnius": c2_const = City.Vilnius
        elif c2 == "Lyon": c2_const = City.Lyon
        else: raise ValueError(f"Unknown city: {c2}")
        allowed_pairs.append( (c1_const, c2_const) )
        allowed_pairs.append( (c2_const, c1_const) )  # bidirectional

    n_days = 20
    # Arrays for each day (0-indexed for 0..19 for days 1..20)
    start = [ Const('start_%d' % i, City) for i in range(n_days) ]
    end = [ Const('end_%d' % i, City) for i in range(n_days) ]
    fly = [ Bool('fly_%d' % i) for i in range(n_days) ]

    solver = Solver()

    # Constraint: start of day1 is Berlin
    solver.add( start[0] == City.Berlin )

    # Flight constraints for each day
    for i in range(n_days):
        # If we fly, then (start[i], end[i]) must be in allowed_pairs, else end[i] = start[i]
        options = []
        for (A, B) in allowed_pairs:
            options.append( And(start[i] == A, end[i] == B) )
        solver.add( If(fly[i], Or(options), start[i] == end[i] ) )
        # Also, if fly[i] is true, then start[i] != end[i]
        solver.add( Implies(fly[i], start[i] != end[i]) )
        # Chain: start of next day is end of current
        if i < n_days-1:
            solver.add( start[i+1] == end[i] )

    # Fixed requirements:

    # Berlin must be present on day1 and day3 (days are 1-indexed, so day3 is index2)
    # Day1: start[0] is Berlin, so automatically present.
    # Day3: either start[2] is Berlin, or we fly on day3 and end[2] is Berlin.
    solver.add( Or(start[2] == City.Berlin, And(fly[2], end[2] == City.Berlin)) )

    # Workshop in Barcelona: must be present on day3 or day4 (index2 or index3)
    in_barcelona_day3 = Or(start[2] == City.Barcelona, And(fly[2], end[2] == City.Barcelona))
    in_barcelona_day4 = Or(start[3] == City.Barcelona, And(fly[3], end[3] == City.Barcelona))
    solver.add( Or(in_barcelona_day3, in_barcelona_day4) )

    # Wedding in Lyon: must be present on day4 or day5 (index3 or index4)
    in_lyon_day4 = Or(start[3] == City.Lyon, And(fly[3], end[3] == City.Lyon))
    in_lyon_day5 = Or(start[4] == City.Lyon, And(fly[4], end[4] == City.Lyon))
    solver.add( Or(in_lyon_day4, in_lyon_day5) )

    # Total days per city
    total_days = {
        City.Berlin: 3,
        City.Nice: 5,
        City.Athens: 5,
        City.Stockholm: 5,
        City.Barcelona: 2,
        City.Vilnius: 4,
        City.Lyon: 2
    }

    for city in cities:
        total = 0
        for i in range(n_days):
            # in_city[i] = Or(start[i] == city, And(fly[i], end[i] == city))
            in_city = Or(start[i] == city, And(fly[i], end[i] == city))
            total += If(in_city, 1, 0)
        solver.add(total == total_days[city])

    # Try to solve
    if solver.check() == sat:
        m = solver.model()
        # Extract the values for each day
        start_vals = [ m.evaluate(start[i]) for i in range(n_days) ]
        end_vals = [ m.evaluate(end[i]) for i in range(n_days) ]
        fly_vals = [ is_true(m.evaluate(fly[i])) for i in range(n_days) ]

        # For each day, the set of cities present
        # Also, for flight days, we will record the two cities for the events
        events = []  # list of (day, city) for flight day events
        # For the contiguous blocks, we will first collect for each city the list of days present
        city_days = {city: [] for city in cities}
        for i in range(n_days):
            day_num = i+1
            # Always present in start[i]
            c_start = start_vals[i]
            city_days[c_start].append(day_num)
            # If fly, also present in end[i]
            if fly_vals[i]:
                c_end = end_vals[i]
                city_days[c_end].append(day_num)
                events.append( (day_num, c_start) )
                events.append( (day_num, c_end) )

        # Now, for each city, find contiguous intervals
        blocks = []  # (start_day, end_day, city)
        for city in cities:
            days_list = sorted(city_days[city])
            if not days_list:
                continue
            start_block = days_list[0]
            for j in range(1, len(days_list)):
                if days_list[j] != days_list[j-1] + 1:
                    # End of current block
                    blocks.append( (start_block, days_list[j-1], city) )
                    start_block = days_list[j]
            blocks.append( (start_block, days_list[-1], city) )

        # Prepare the list of records for the itinerary
        records = []  # each record: (sort_key, type, day_range_str, city_str)

        # For blocks: we create a record for each block
        for (start_day, end_day, city) in blocks:
            if start_day == end_day:
                day_range_str = "Day " + str(start_day)
            else:
                day_range_str = "Day " + str(start_day) + '-' + str(end_day)
            city_str = city_names[city]
            # For sorting: use start_day, and mark as 'block'
            records.append( (start_day, 'block', day_range_str, city_str) )

        # For events: each event is a (day, city)
        for (day, city) in events:
            day_range_str = "Day " + str(day)
            city_str = city_names[city]
            records.append( (day, 'event', day_range_str, city_str) )

        # Sort records: by the day (first element) and then by type: events before blocks for the same day
        # We can use a tuple (day, type) where 'event' < 'block'
        records_sorted = sorted(records, key=lambda r: (r[0], 0 if r[1]=='event' else 1))

        # Now extract the itinerary list of dictionaries
        itinerary_list = []
        for rec in records_sorted:
            # rec[2] is the day_range_str, rec[3] is the city_str
            itinerary_list.append( {"day_range": rec[2], "place": rec[3]} )

        # Output as JSON-like dictionary
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        # Try with strict constraints for Barcelona and Lyon
        solver2 = Solver()
        # Same setup as before, except for Barcelona and Lyon
        solver2.add( start[0] == City.Berlin )
        for i in range(n_days):
            options = []
            for (A, B) in allowed_pairs:
                options.append( And(start[i] == A, end[i] == B) )
            solver2.add( If(fly[i], Or(options), start[i] == end[i] ) )
            solver2.add( Implies(fly[i], start[i] != end[i]) )
            if i < n_days-1:
                solver2.add( start[i+1] == end[i] )
        # Berlin on day3
        solver2.add( Or(start[2] == City.Berlin, And(fly[2], end[2] == City.Berlin)) )
        # Barcelona must be present on day4 (index3)
        in_barcelona_day4 = Or(start[3] == City.Barcelona, And(fly[3], end[3] == City.Barcelona))
        solver2.add( in_barcelona_day4 )
        # Lyon must be present on day5 (index4)
        in_lyon_day5 = Or(start[4] == City.Lyon, And(fly[4], end[4] == City.Lyon))
        solver2.add( in_lyon_day5 )
        # Total days
        for city in cities:
            total = 0
            for i in range(n_days):
                in_city = Or(start[i] == city, And(fly[i], end[i] == city))
                total += If(in_city, 1, 0)
            solver2.add(total == total_days[city])
        
        if solver2.check() == sat:
            m = solver2.model()
            start_vals = [ m.evaluate(start[i]) for i in range(n_days) ]
            end_vals = [ m.evaluate(end[i]) for i in range(n_days) ]
            fly_vals = [ is_true(m.evaluate(fly[i])) for i in range(n_days) ]

            events = []
            city_days = {city: [] for city in cities}
            for i in range(n_days):
                day_num = i+1
                c_start = start_vals[i]
                city_days[c_start].append(day_num)
                if fly_vals[i]:
                    c_end = end_vals[i]
                    city_days[c_end].append(day_num)
                    events.append( (day_num, c_start) )
                    events.append( (day_num, c_end) )

            blocks = []
            for city in cities:
                days_list = sorted(city_days[city])
                if not days_list:
                    continue
                start_block = days_list[0]
                for j in range(1, len(days_list)):
                    if days_list[j] != days_list[j-1] + 1:
                        blocks.append( (start_block, days_list[j-1], city) )
                        start_block = days_list[j]
                blocks.append( (start_block, days_list[-1], city) )

            records = []
            for (start_day, end_day, city) in blocks:
                if start_day == end_day:
                    day_range_str = "Day " + str(start_day)
                else:
                    day_range_str = "Day " + str(start_day) + '-' + str(end_day)
                city_str = city_names[city]
                records.append( (start_day, 'block', day_range_str, city_str) )
            for (day, city) in events:
                day_range_str = "Day " + str(day)
                city_str = city_names[city]
                records.append( (day, 'event', day_range_str, city_str) )

            records_sorted = sorted(records, key=lambda r: (r[0], 0 if r[1]=='event' else 1))
            itinerary_list = []
            for rec in records_sorted:
                itinerary_list.append( {"day_range": rec[2], "place": rec[3]} )
            result = {"itinerary": itinerary_list}
            print(result)
        else:
            print("No solution found")

if __name__ == "__main__":
    main()