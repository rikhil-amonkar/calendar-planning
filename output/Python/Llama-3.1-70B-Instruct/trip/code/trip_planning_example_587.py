import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Attend wedding in Manchester
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Manchester"] - 1}', 'place': 'Manchester'})
    visited_cities.add('Manchester')
    current_day += city_stay["Manchester"]

    # Visit Venice
    if 'Venice' in direct_flights['Manchester']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Manchester', 'to': 'Venice'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Venice"] - 1}', 'place': 'Venice'})
        visited_cities.add('Venice')
        current_day += city_stay["Venice"]
    else:
        raise Exception("No direct flight from Manchester to Venice")

    # Visit Istanbul
    if 'Istanbul' in direct_flights['Venice']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Venice', 'to': 'Istanbul'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Istanbul"] - 1}', 'place': 'Istanbul'})
        visited_cities.add('Istanbul')
        current_day += city_stay["Istanbul"]
    else:
        raise Exception("No direct flight from Venice to Istanbul")

    # Visit Krakow
    if 'Krakow' in direct_flights['Istanbul']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Istanbul', 'to': 'Krakow'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Krakow"] - 1}', 'place': 'Krakow'})
        visited_cities.add('Krakow')
        current_day += city_stay["Krakow"]
    else:
        raise Exception("No direct flight from Istanbul to Krakow")

    # Visit Lyon
    if 'Lyon' in direct_flights['Krakow']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Lyon'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Lyon"] - 1}', 'place': 'Lyon'})
        visited_cities.add('Lyon')
        current_day += city_stay["Lyon"]
    else:
        raise Exception("No direct flight from Krakow to Lyon")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }

    direct_flights = {
        "Manchester": ["Venice", "Istanbul", "Krakow"],
        "Istanbul": ["Krakow", "Venice"],
        "Venice": ["Istanbul", "Lyon"],
        "Krakow": ["Lyon"],
        "Lyon": ["Istanbul"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()