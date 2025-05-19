import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit relatives in Athens
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Athens"] - 1}', 'place': 'Athens'})
    visited_cities.add('Athens')
    current_day += city_stay["Athens"]

    # Visit Valencia
    if 'Valencia' in direct_flights['Athens']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Athens', 'to': 'Valencia'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Valencia"] - 1}', 'place': 'Valencia'})
        visited_cities.add('Valencia')
        current_day += city_stay["Valencia"]
    else:
        raise Exception("No direct flight from Athens to Valencia")

    # Visit Zurich
    if 'Zurich' in direct_flights['Valencia']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Valencia', 'to': 'Zurich'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Zurich"] - 1}', 'place': 'Zurich'})
        visited_cities.add('Zurich')
        current_day += city_stay["Zurich"]
    else:
        raise Exception("No direct flight from Valencia to Zurich")

    # Visit Naples
    if 'Naples' in direct_flights['Zurich']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Zurich', 'to': 'Naples'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Naples"] - 1}', 'place': 'Naples'})
        visited_cities.add('Naples')
        current_day += city_stay["Naples"]
    else:
        raise Exception("No direct flight from Zurich to Naples")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6
    }

    direct_flights = {
        "Valencia": ["Naples", "Athens"],
        "Athens": ["Naples", "Zurich", "Valencia"],
        "Naples": ["Zurich", "Athens"],
        "Zurich": ["Naples", "Athens", "Valencia"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()