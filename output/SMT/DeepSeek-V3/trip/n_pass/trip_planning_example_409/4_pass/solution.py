from z3 import *

def solve_itinerary():
    # Cities encoding
    cities = {
        'Zurich': 0,
        'Helsinki': 1,
        'Hamburg': 2,
        'Bucharest': 3,
        'Split': 4
    }
    num_cities = len(cities)
    num_days = 12

    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3, 4],  # Zurich
        1: [0, 2, 4],      # Helsinki
        2: [1, 3, 0, 4],   # Hamburg
        3: [2, 0],         # Bucharest
        4: [0, 1, 2]       # Split
    }

    # Create Z3 variables: day[i] is the city on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(num_days)]

    s = Solver()

    # Each day's city must be valid (0 to 4)
    for d in day:
        s.add(And(d >= 0, d < num_cities))

    # Flight transitions: consecutive days must be connected by direct flights or same city
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Create a list of possible next cities including the current city
        possible_next = [current_city == next_city]
        for j in direct_flights.get(current_city.as_long() if hasattr(current_city, 'as_long') else current_city, []):
            possible_next.append(next_city == j)
        s.add(Or(possible_next))

    # Total days per city constraints
    for city_name, city_code in cities.items():
        if city_name == 'Zurich':
            total = 3
        elif city_name == 'Hamburg':
            total = 2
        elif city_name == 'Helsinki':
            total = 2
        elif city_name == 'Bucharest':
            total = 2
        elif city_name == 'Split':
            total = 7
        else:
            total = 0
        s.add(Sum([If(day[i] == city_code, 1, 0) for i in range(num_days)]) == total)

    # Wedding in Zurich between day 1 and 3: at least one of days 0,1,2 (0-based) is Zurich
    s.add(Or(day[0] == cities['Zurich'], day[1] == cities['Zurich'], day[2] == cities['Zurich']))

    # Conference in Split on day 4 and day 10 (1-based: days 3 and 9 in 0-based)
    s.add(day[3] == cities['Split'])
    s.add(day[9] == cities['Split'])

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        day_place = {}
        for i in range(num_days):
            city_code = model.evaluate(day[i]).as_long()
            city_name = [name for name, code in cities.items() if code == city_code][0]
            day_place[i + 1] = city_name  # 1-based days

        # Generate the itinerary
        itinerary = []
        current_city = day_place[1]
        start_day = 1
        for day_num in range(2, num_days + 1):
            if day_place[day_num] != current_city:
                # Add the stay in current_city from start_day to day_num-1
                if start_day == day_num - 1:
                    itinerary.append({'day_range': f'Day {start_day}', 'place': current_city})
                else:
                    itinerary.append({'day_range': f'Day {start_day}-{day_num - 1}', 'place': current_city})
                # Add the flight day: departure and arrival
                itinerary.append({'day_range': f'Day {day_num - 1}', 'place': current_city})
                itinerary.append({'day_range': f'Day {day_num - 1}', 'place': day_place[day_num]})
                current_city = day_place[day_num]
                start_day = day_num
        # Add the last stay
        if start_day == num_days:
            itinerary.append({'day_range': f'Day {start_day}', 'place': current_city})
        else:
            itinerary.append({'day_range': f'Day {start_day}-{num_days}', 'place': current_city})

        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)