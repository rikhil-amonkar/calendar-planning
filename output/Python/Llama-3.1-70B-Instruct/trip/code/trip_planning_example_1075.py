import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Vienna
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Vienna"] - 1}', 'place': 'Vienna'})
    visited_cities.add('Vienna')
    current_day += city_stay["Vienna"]

    # Visit Lyon
    if 'Lyon' in direct_flights['Vienna']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Lyon'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Lyon"] - 1}', 'place': 'Lyon'})
        visited_cities.add('Lyon')
        current_day += city_stay["Lyon"]
    else:
        raise Exception("No direct flight from Vienna to Lyon")

    # Visit Prague
    if 'Prague' in direct_flights['Lyon']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Prague'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Prague"] - 1}', 'place': 'Prague'})
        visited_cities.add('Prague')
        current_day += city_stay["Prague"]
    else:
        raise Exception("No direct flight from Lyon to Prague")

    # Visit Edinburgh
    if 'Edinburgh' in direct_flights['Prague']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Prague', 'to': 'Edinburgh'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Edinburgh"] - 1}', 'place': 'Edinburgh'})
        visited_cities.add('Edinburgh')
        current_day += city_stay["Edinburgh"]
    else:
        raise Exception("No direct flight from Prague to Edinburgh")

    # Visit Manchester
    if 'Manchester' in direct_flights['Edinburgh']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Edinburgh', 'to': 'Manchester'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Manchester"] - 1}', 'place': 'Manchester'})
        visited_cities.add('Manchester')
        current_day += city_stay["Manchester"]
    else:
        raise Exception("No direct flight from Edinburgh to Manchester")

    # Visit Reykjavik
    if 'Reykjavik' in direct_flights['Manchester']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Manchester', 'to': 'Reykjavik'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Reykjavik"] - 1}', 'place': 'Reykjavik'})
        visited_cities.add('Reykjavik')
        current_day += city_stay["Reykjavik"]
    else:
        raise Exception("No direct flight from Manchester to Reykjavik")

    # Visit Stuttgart
    if 'Stuttgart' in direct_flights['Reykjavik']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Stuttgart'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Stuttgart"] - 1}', 'place': 'Stuttgart'})
        visited_cities.add('Stuttgart')
        current_day += city_stay["Stuttgart"]
    else:
        raise Exception("No direct flight from Reykjavik to Stuttgart")

    # Visit Split
    if 'Split' in direct_flights['Stuttgart']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stuttgart', 'to': 'Split'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Split"] - 1}', 'place': 'Split'})
        visited_cities.add('Split')
        current_day += city_stay["Split"]
    else:
        raise Exception("No direct flight from Stuttgart to Split")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }

    direct_flights = {
        "Reykjavik": ["Stuttgart", "Vienna"],
        "Stuttgart": ["Split", "Vienna", "Edinburgh", "Manchester"],
        "Prague": ["Manchester", "Vienna", "Split", "Lyon", "Reykjavik"],
        "Edinburgh": ["Prague"],
        "Manchester": ["Split", "Prague"],
        "Lyon": ["Split", "Vienna"],
        "Vienna": ["Manchester", "Lyon", "Split", "Stuttgart", "Reykjavik", "Prague"],
        "Split": ["Lyon", "Vienna"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()