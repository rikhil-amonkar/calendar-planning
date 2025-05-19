import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Amsterdam
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Amsterdam"] - 1}', 'place': 'Amsterdam'})
    visited_cities.add('Amsterdam')
    current_day += city_stay["Amsterdam"]

    # Visit Edinburgh
    if 'Edinburgh' in direct_flights['Amsterdam']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Amsterdam', 'to': 'Edinburgh'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Edinburgh"] - 1}', 'place': 'Edinburgh'})
        visited_cities.add('Edinburgh')
        current_day += city_stay["Edinburgh"]
    else:
        raise Exception("No direct flight from Amsterdam to Edinburgh")

    # Visit Brussels
    if 'Brussels' in direct_flights['Edinburgh']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Edinburgh', 'to': 'Brussels'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Brussels"] - 1}', 'place': 'Brussels'})
        visited_cities.add('Brussels')
        current_day += city_stay["Brussels"]
    else:
        raise Exception("No direct flight from Edinburgh to Brussels")

    # Visit Vienna
    if 'Vienna' in direct_flights['Brussels']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Brussels', 'to': 'Vienna'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Vienna"] - 1}', 'place': 'Vienna'})
        visited_cities.add('Vienna')
        current_day += city_stay["Vienna"]
    else:
        raise Exception("No direct flight from Brussels to Vienna")

    # Visit Berlin
    if 'Berlin' in direct_flights['Vienna']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Berlin'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Berlin"] - 1}', 'place': 'Berlin'})
        visited_cities.add('Berlin')
        current_day += city_stay["Berlin"]
    else:
        raise Exception("No direct flight from Vienna to Berlin")

    # Visit Reykjavik
    if 'Reykjavik' in direct_flights['Berlin']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Berlin', 'to': 'Reykjavik'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Reykjavik"] - 1}', 'place': 'Reykjavik'})
        visited_cities.add('Reykjavik')
        current_day += city_stay["Reykjavik"]
    else:
        raise Exception("No direct flight from Berlin to Reykjavik")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5
    }

    direct_flights = {
        "Edinburgh": ["Berlin", "Amsterdam", "Brussels"],
        "Amsterdam": ["Berlin", "Edinburgh", "Reykjavik", "Vienna"],
        "Vienna": ["Berlin", "Brussels", "Reykjavik"],
        "Berlin": ["Brussels", "Reykjavik", "Edinburgh", "Amsterdam"],
        "Brussels": ["Vienna", "Reykjavik", "Edinburgh", "Amsterdam"],
        "Reykjavik": ["Vienna", "Berlin", "Amsterdam", "Brussels"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()