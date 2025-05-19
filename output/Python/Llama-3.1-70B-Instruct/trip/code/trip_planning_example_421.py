import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit relatives in Nice
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Nice"] - 1}', 'place': 'Nice'})
    visited_cities.add('Nice')
    current_day += city_stay["Nice"]

    # Visit Lyon
    if 'Lyon' in direct_flights['Nice']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Nice', 'to': 'Lyon'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Lyon"] - 1}', 'place': 'Lyon'})
        visited_cities.add('Lyon')
        current_day += city_stay["Lyon"]
    else:
        raise Exception("No direct flight from Nice to Lyon")

    # Visit Dublin
    if 'Dublin' in direct_flights['Lyon']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Dublin'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Dublin"] - 1}', 'place': 'Dublin'})
        visited_cities.add('Dublin')
        current_day += city_stay["Dublin"]
    else:
        raise Exception("No direct flight from Lyon to Dublin")

    # Visit Krakow
    if 'Krakow' in direct_flights['Dublin']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dublin', 'to': 'Krakow'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Krakow"] - 1}', 'place': 'Krakow'})
        visited_cities.add('Krakow')
        current_day += city_stay["Krakow"]
    else:
        raise Exception("No direct flight from Dublin to Krakow")

    # Visit Frankfurt
    if 'Frankfurt' in direct_flights['Krakow']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Frankfurt'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Frankfurt"] - 1}', 'place': 'Frankfurt'})
        visited_cities.add('Frankfurt')
        current_day += city_stay["Frankfurt"]
    else:
        raise Exception("No direct flight from Krakow to Frankfurt")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }

    direct_flights = {
        "Nice": ["Dublin", "Frankfurt", "Lyon"],
        "Dublin": ["Frankfurt", "Krakow", "Lyon", "Nice"],
        "Krakow": ["Frankfurt", "Dublin"],
        "Lyon": ["Frankfurt", "Dublin", "Nice"],
        "Frankfurt": ["Dublin", "Krakow", "Lyon", "Nice"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()