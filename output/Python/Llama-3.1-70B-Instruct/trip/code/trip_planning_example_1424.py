import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Attend workshop in Porto
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Porto"] - 1}', 'place': 'Porto'})
    visited_cities.add('Porto')
    current_day += city_stay["Porto"]

    # Visit relatives in Amsterdam
    if 'Amsterdam' in direct_flights['Porto']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Porto', 'to': 'Amsterdam'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Amsterdam"] - 1}', 'place': 'Amsterdam'})
        visited_cities.add('Amsterdam')
        current_day += city_stay["Amsterdam"]
    else:
        raise Exception("No direct flight from Porto to Amsterdam")

    # Attend wedding in Helsinki
    if 'Helsinki' in direct_flights['Amsterdam']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Amsterdam', 'to': 'Helsinki'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Helsinki"] - 1}', 'place': 'Helsinki'})
        visited_cities.add('Helsinki')
        current_day += city_stay["Helsinki"]
    else:
        raise Exception("No direct flight from Amsterdam to Helsinki")

    # Visit Reykjavik
    if 'Reykjavik' in direct_flights['Helsinki']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Helsinki', 'to': 'Reykjavik'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Reykjavik"] - 1}', 'place': 'Reykjavik'})
        visited_cities.add('Reykjavik')
        current_day += city_stay["Reykjavik"]
    else:
        raise Exception("No direct flight from Helsinki to Reykjavik")

    # Visit Warsaw
    if 'Warsaw' in direct_flights['Reykjavik']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Warsaw'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Warsaw"] - 1}', 'place': 'Warsaw'})
        visited_cities.add('Warsaw')
        current_day += city_stay["Warsaw"]
    else:
        raise Exception("No direct flight from Reykjavik to Warsaw")

    # Visit Brussels
    if 'Brussels' in direct_flights['Warsaw']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Warsaw', 'to': 'Brussels'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Brussels"] - 1}', 'place': 'Brussels'})
        visited_cities.add('Brussels')
        current_day += city_stay["Brussels"]
    else:
        raise Exception("No direct flight from Warsaw to Brussels")

    # Visit Lyon
    if 'Lyon' in direct_flights['Brussels']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Brussels', 'to': 'Lyon'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Lyon"] - 1}', 'place': 'Lyon'})
        visited_cities.add('Lyon')
        current_day += city_stay["Lyon"]
    else:
        raise Exception("No direct flight from Brussels to Lyon")

    # Visit Split
    if 'Split' in direct_flights['Lyon']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Split'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Split"] - 1}', 'place': 'Split'})
        visited_cities.add('Split')
        current_day += city_stay["Split"]
    else:
        raise Exception("No direct flight from Lyon to Split")

    # Visit Naples
    if 'Naples' in direct_flights['Split']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Naples'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Naples"] - 1}', 'place': 'Naples'})
        visited_cities.add('Naples')
        current_day += city_stay["Naples"]
    else:
        raise Exception("No direct flight from Split to Naples")

    # Visit Valencia
    if 'Valencia' in direct_flights['Naples']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Naples', 'to': 'Valencia'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Valencia"] - 1}', 'place': 'Valencia'})
        visited_cities.add('Valencia')
        current_day += city_stay["Valencia"]
    else:
        raise Exception("No direct flight from Naples to Valencia")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Warsaw": 3,
        "Porto": 5,
        "Naples": 4,
        "Brussels": 3,
        "Split": 3,
        "Reykjavik": 5,
        "Amsterdam": 4,
        "Lyon": 3,
        "Helsinki": 4,
        "Valencia": 2
    }

    direct_flights = {
        "Amsterdam": ["Warsaw", "Lyon", "Naples", "Reykjavik", "Split", "Helsinki", "Valencia"],
        "Helsinki": ["Brussels", "Warsaw", "Split", "Naples", "Reykjavik"],
        "Reykjavik": ["Brussels", "Warsaw"],
        "Naples": ["Valencia", "Split", "Brussels"],
        "Porto": ["Brussels", "Amsterdam", "Lyon", "Warsaw", "Valencia"],
        "Split": ["Lyon", "Warsaw", "Naples"],
        "Warsaw": ["Split", "Valencia", "Brussels", "Naples"],
        "Brussels": ["Lyon", "Valencia"],
        "Lyon": ["Split"],
        "Valencia": ["Lyon"],
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()