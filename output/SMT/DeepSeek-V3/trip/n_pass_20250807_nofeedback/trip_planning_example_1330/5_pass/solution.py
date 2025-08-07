from z3 import *
import json

def solve_itinerary():
    # Cities with their required stay durations
    cities = {
        'Salzburg': 2,
        'Venice': 5,
        'Bucharest': 4,
        'Brussels': 2,
        'Hamburg': 4,
        'Copenhagen': 4,
        'Nice': 3,
        'Zurich': 5,
        'Naples': 4
    }
    city_list = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_list)}

    # Corrected direct flight connections
    direct_flights = {
        'Zurich': ['Brussels', 'Nice', 'Naples', 'Copenhagen', 'Bucharest', 'Venice'],
        'Brussels': ['Zurich', 'Venice', 'Bucharest', 'Hamburg', 'Nice', 'Copenhagen', 'Naples'],
        'Bucharest': ['Copenhagen', 'Brussels', 'Hamburg', 'Naples', 'Zurich'],
        'Venice': ['Brussels', 'Naples', 'Copenhagen', 'Zurich', 'Nice', 'Hamburg'],
        'Nice': ['Zurich', 'Hamburg', 'Brussels', 'Venice', 'Naples', 'Copenhagen'],
        'Hamburg': ['Nice', 'Bucharest', 'Brussels', 'Zurich', 'Copenhagen', 'Venice', 'Salzburg'],
        'Copenhagen': ['Bucharest', 'Brussels', 'Venice', 'Zurich', 'Hamburg', 'Naples', 'Nice'],
        'Naples': ['Zurich', 'Venice', 'Bucharest', 'Brussels', 'Copenhagen', 'Nice', 'Hamburg'],
        'Salzburg': ['Hamburg']
    }

    # Z3 solver
    s = Solver()

    # Variables: day 1 to 25, each is one of the cities
    days = [Int(f'day_{i}') for i in range(1, 26)]
    for day in days:
        s.add(day >= 0, day < len(city_list))

    # Helper functions
    def city_constraint(day, city):
        return days[day-1] == city_to_idx[city]

    def count_days_in_city(city):
        return Sum([If(days[i] == city_to_idx[city], 1, 0) for i in range(25)])

    # Fixed constraints:
    # Nice between day 9-11
    s.add(city_constraint(9, 'Nice'))
    s.add(city_constraint(10, 'Nice'))
    s.add(city_constraint(11, 'Nice'))

    # Copenhagen between day 18-21 (wedding)
    s.add(city_constraint(18, 'Copenhagen'))
    s.add(city_constraint(19, 'Copenhagen'))
    s.add(city_constraint(20, 'Copenhagen'))
    s.add(city_constraint(21, 'Copenhagen'))

    # Brussels between day 21-22 (meet friends)
    s.add(city_constraint(21, 'Brussels'))
    s.add(city_constraint(22, 'Brussels'))

    # Naples between day 22-25 (workshop)
    s.add(city_constraint(22, 'Naples'))
    s.add(city_constraint(23, 'Naples'))
    s.add(city_constraint(24, 'Naples'))
    s.add(city_constraint(25, 'Naples'))

    # Duration constraints:
    for city, duration in cities.items():
        s.add(count_days_in_city(city) == duration)

    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(24):
        current_day = days[i]
        next_day = days[i+1]
        same_city = current_day == next_day
        flight_possible = Or([And(current_day == city_to_idx[city], 
                                next_day == city_to_idx[neighbor])
                            for city in direct_flights 
                            for neighbor in direct_flights[city]])
        s.add(Or(same_city, flight_possible))

    # Additional constraints to help the solver find a solution
    # Start in Zurich (well-connected city)
    s.add(days[0] == city_to_idx['Zurich'])
    # Ensure we visit Salzburg by day 10 (to allow flexibility)
    s.add(Or([days[i] == city_to_idx['Salzburg'] for i in range(10)]))
    # Ensure we visit Venice before day 15
    s.add(Or([days[i] == city_to_idx['Venice'] for i in range(15)]))
    # Ensure we visit Bucharest before day 17
    s.add(Or([days[i] == city_to_idx['Bucharest'] for i in range(17)]))

    # Solve with a time limit (in milliseconds)
    s.set("timeout", 30000)  # 30 seconds timeout
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 26):
            city_idx = model.evaluate(days[day-1]).as_long()
            itinerary.append({'day': day, 'place': city_list[city_idx]})
        
        # Verify all constraints are met
        city_counts = {city: 0 for city in city_list}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        for city, count in city_counts.items():
            assert count == cities[city], f"Duration mismatch for {city}"
        
        # Verify flight connections
        for i in range(24):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current_city != next_city:
                assert next_city in direct_flights[current_city], \
                    f"No direct flight from {current_city} to {next_city} on day {i+1}"
        
        # Output as JSON
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found within time limit")

solve_itinerary()