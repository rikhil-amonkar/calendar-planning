import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Split
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Split"] - 1}', 'place': 'Split'})
    visited_cities.add('Split')
    current_day += city_stay["Split"]

    # Visit Munich
    if 'Munich' in direct_flights['Split']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Munich'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Munich"] - 1}', 'place': 'Munich'})
        visited_cities.add('Munich')
        current_day += city_stay["Munich"]
    else:
        raise Exception("No direct flight from Split to Munich")

    # Visit Lyon
    if 'Lyon' in direct_flights['Munich']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Munich', 'to': 'Lyon'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Lyon"] - 1}', 'place': 'Lyon'})
        visited_cities.add('Lyon')
        current_day += city_stay["Lyon"]
    else:
        raise Exception("No direct flight from Munich to Lyon")

    # Visit Hamburg
    if 'Hamburg' in direct_flights['Split']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Hamburg'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Hamburg"] - 1}', 'place': 'Hamburg'})
        visited_cities.add('Hamburg')
        current_day += city_stay["Hamburg"]
    else:
        raise Exception("No direct flight from Lyon to Hamburg")

    # Visit Manchester
    if 'Manchester' in direct_flights['Hamburg']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Hamburg', 'to': 'Manchester'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Manchester"] - 1}', 'place': 'Manchester'})
        visited_cities.add('Manchester')
        current_day += city_stay["Manchester"]
    else:
        raise Exception("No direct flight from Hamburg to Manchester")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Hamburg": 7,
        "Munich": 6,
        "Manchester": 2,
        "Lyon": 2,
        "Split": 7
    }

    direct_flights = {
        "Split": ["Munich", "Lyon", "Hamburg", "Manchester"],
        "Munich": ["Manchester", "Lyon", "Split"],
        "Hamburg": ["Manchester", "Munich", "Split"],
        "Lyon": ["Munich", "Split"],
        "Manchester": ["Split"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()