import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Madrid
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Madrid"] - 1}', 'place': 'Madrid'})
    visited_cities.add('Madrid')
    current_day += city_stay["Madrid"]

    # Visit Berlin
    if 'Berlin' in direct_flights['Madrid']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Madrid', 'to': 'Berlin'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Berlin"] - 1}', 'place': 'Berlin'})
        visited_cities.add('Berlin')
        current_day += city_stay["Berlin"]
    else:
        raise Exception("No direct flight from Madrid to Berlin")

    # Visit London
    if 'London' in direct_flights['Berlin']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Berlin', 'to': 'London'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["London"] - 1}', 'place': 'London'})
        visited_cities.add('London')
        current_day += city_stay["London"]
    else:
        raise Exception("No direct flight from Berlin to London")

    # Visit Dublin
    if 'Dublin' in direct_flights['London']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'London', 'to': 'Dublin'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Dublin"] - 1}', 'place': 'Dublin'})
        visited_cities.add('Dublin')
        current_day += city_stay["Dublin"]
    else:
        raise Exception("No direct flight from London to Dublin")

    # Visit Oslo
    if 'Oslo' in direct_flights['Dublin']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dublin', 'to': 'Oslo'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Oslo"] - 1}', 'place': 'Oslo'})
        visited_cities.add('Oslo')
        current_day += city_stay["Oslo"]
    else:
        raise Exception("No direct flight from Dublin to Oslo")

    # Visit Vilnius
    if 'Vilnius' in direct_flights['Oslo']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Vilnius'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Vilnius"] - 1}', 'place': 'Vilnius'})
        visited_cities.add('Vilnius')
        current_day += city_stay["Vilnius"]
    else:
        raise Exception("No direct flight from Oslo to Vilnius")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5
    }

    direct_flights = {
        "London": ["Madrid", "Oslo"],
        "Oslo": ["Vilnius", "Madrid"],
        "Berlin": ["Vilnius", "Oslo", "Madrid", "Dublin", "London"],
        "Madrid": ["Oslo", "London", "Dublin", "Berlin"],
        "Dublin": ["Oslo", "London", "Berlin"],
        "Vilnius": ["Oslo", "Berlin"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()