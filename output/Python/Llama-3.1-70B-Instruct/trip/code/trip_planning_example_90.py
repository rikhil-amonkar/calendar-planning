import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Naples
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Naples"] - 1}', 'place': 'Naples'})
    visited_cities.add('Naples')
    current_day += city_stay["Naples"]

    # Visit Vienna
    if 'Vienna' in direct_flights['Naples']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Naples', 'to': 'Vienna'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Vienna"] - 1}', 'place': 'Vienna'})
        visited_cities.add('Vienna')
        current_day += city_stay["Vienna"]
    else:
        raise Exception("No direct flight from Naples to Vienna")

    # Visit Vilnius
    if 'Vilnius' in direct_flights['Vienna']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Vilnius'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Vilnius"] - 1}', 'place': 'Vilnius'})
        visited_cities.add('Vilnius')
        current_day += city_stay["Vilnius"]
    else:
        raise Exception("No direct flight from Vienna to Vilnius")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Vilnius": 7,
        "Naples": 5,
        "Vienna": 7
    }

    direct_flights = {
        "Naples": ["Vienna"],
        "Vienna": ["Vilnius", "Naples"],
        "Vilnius": ["Vienna"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()