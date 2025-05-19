import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Paris
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Paris"] - 1}', 'place': 'Paris'})
    visited_cities.add('Paris')
    current_day += city_stay["Paris"]

    # Visit Amsterdam
    if 'Amsterdam' in direct_flights['Paris']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Paris', 'to': 'Amsterdam'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Amsterdam"] - 1}', 'place': 'Amsterdam'})
        visited_cities.add('Amsterdam')
        current_day += city_stay["Amsterdam"]
    else:
        raise Exception("No direct flight from Paris to Amsterdam")

    # Visit Geneva
    if 'Geneva' in direct_flights['Amsterdam']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Amsterdam', 'to': 'Geneva'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Geneva"] - 1}', 'place': 'Geneva'})
        visited_cities.add('Geneva')
        current_day += city_stay["Geneva"]
    else:
        raise Exception("No direct flight from Amsterdam to Geneva")

    # Visit Munich
    if 'Munich' in direct_flights['Geneva']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Geneva', 'to': 'Munich'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Munich"] - 1}', 'place': 'Munich'})
        visited_cities.add('Munich')
        current_day += city_stay["Munich"]
    else:
        raise Exception("No direct flight from Geneva to Munich")

    # Visit Split
    if 'Split' in direct_flights['Munich']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Munich', 'to': 'Split'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Split"] - 1}', 'place': 'Split'})
        visited_cities.add('Split')
        current_day += city_stay["Split"]
    else:
        raise Exception("No direct flight from Munich to Split")

    # Visit Krakow
    if 'Krakow' in direct_flights['Split']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Krakow'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Krakow"] - 1}', 'place': 'Krakow'})
        visited_cities.add('Krakow')
        current_day += city_stay["Krakow"]
    else:
        raise Exception("No direct flight from Split to Krakow")

    # Visit Vilnius
    if 'Vilnius' in direct_flights['Krakow']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Vilnius'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Vilnius"] - 1}', 'place': 'Vilnius'})
        visited_cities.add('Vilnius')
        current_day += city_stay["Vilnius"]
    else:
        raise Exception("No direct flight from Krakow to Vilnius")

    # Visit Budapest
    if 'Budapest' in direct_flights['Vilnius']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vilnius', 'to': 'Budapest'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Budapest"] - 1}', 'place': 'Budapest'})
        visited_cities.add('Budapest')
        current_day += city_stay["Budapest"]
    else:
        raise Exception("No direct flight from Vilnius to Budapest")

    # Visit Santorini
    if 'Santorini' in direct_flights['Budapest']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Budapest', 'to': 'Santorini'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Santorini"] - 1}', 'place': 'Santorini'})
        visited_cities.add('Santorini')
        current_day += city_stay["Santorini"]
    else:
        raise Exception("No direct flight from Budapest to Santorini")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4
    }

    direct_flights = {
        "Paris": ["Krakow", "Amsterdam", "Split", "Geneva"],
        "Amsterdam": ["Geneva"],
        "Geneva": ["Munich"],
        "Munich": ["Split", "Amsterdam", "Budapest", "Paris"],
        "Split": ["Krakow", "Geneva", "Amsterdam"],
        "Krakow": ["Amsterdam", "Vilnius"],
        "Vilnius": ["Munich", "Split", "Amsterdam", "Paris"],
        "Budapest": ["Amsterdam", "Paris", "Geneva"],
        "Santorini": ["Geneva", "Amsterdam"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()