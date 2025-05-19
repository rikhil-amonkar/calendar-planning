import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Reykjavik
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Reykjavik"] - 1}', 'place': 'Reykjavik'})
    visited_cities.add('Reykjavik')
    current_day += city_stay["Reykjavik"]

    # Visit Oslo
    if 'Oslo' in direct_flights['Reykjavik']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Oslo'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Oslo"] - 1}', 'place': 'Oslo'})
        visited_cities.add('Oslo')
        current_day += city_stay["Oslo"]
    else:
        raise Exception("No direct flight from Reykjavik to Oslo")

    # Visit Dubrovnik
    if 'Dubrovnik' in direct_flights['Oslo']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Dubrovnik'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Dubrovnik"] - 1}', 'place': 'Dubrovnik'})
        visited_cities.add('Dubrovnik')
        current_day += city_stay["Dubrovnik"]
    else:
        raise Exception("No direct flight from Oslo to Dubrovnik")

    # Visit Madrid
    if 'Madrid' in direct_flights['Dubrovnik']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dubrovnik', 'to': 'Madrid'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Madrid"] - 1}', 'place': 'Madrid'})
        visited_cities.add('Madrid')
        current_day += city_stay["Madrid"]
    else:
        raise Exception("No direct flight from Dubrovnik to Madrid")

    # Visit Lyon
    if 'Lyon' in direct_flights['Madrid']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Madrid', 'to': 'Lyon'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Lyon"] - 1}', 'place': 'Lyon'})
        visited_cities.add('Lyon')
        current_day += city_stay["Lyon"]
    else:
        raise Exception("No direct flight from Madrid to Lyon")

    # Visit London
    if 'London' in direct_flights['Lyon']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'London'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["London"] - 1}', 'place': 'London'})
        visited_cities.add('London')
        current_day += city_stay["London"]
    else:
        raise Exception("No direct flight from Lyon to London")

    # Visit Warsaw
    if 'Warsaw' in direct_flights['London']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'London', 'to': 'Warsaw'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Warsaw"] - 1}', 'place': 'Warsaw'})
        visited_cities.add('Warsaw')
        current_day += city_stay["Warsaw"]
    else:
        raise Exception("No direct flight from London to Warsaw")

    # Visit Riga
    if 'Riga' in direct_flights['Warsaw']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Warsaw', 'to': 'Riga'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Riga"] - 1}', 'place': 'Riga'})
        visited_cities.add('Riga')
        current_day += city_stay["Riga"]
    else:
        raise Exception("No direct flight from Warsaw to Riga")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3
    }

    direct_flights = {
        "Warsaw": ["Reykjavik", "Riga", "Oslo", "London", "Madrid"],
        "Oslo": ["Madrid", "Dubrovnik", "Reykjavik", "Riga", "Lyon", "London"],
        "Lyon": ["London", "Madrid"],
        "Madrid": ["London", "Lyon", "Dubrovnik"],
        "Reykjavik": ["Warsaw", "Madrid", "Oslo"],
        "London": ["Reykjavik", "Warsaw", "Madrid", "Lyon", "Oslo"],
        "Dubrovnik": ["Madrid"],
        "Riga": ["Oslo", "Warsaw"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()