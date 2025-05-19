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

    # Visit Athens
    if 'Athens' in direct_flights['Naples']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Naples', 'to': 'Athens'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Athens"] - 1}', 'place': 'Athens'})
        visited_cities.add('Athens')
        current_day += city_stay["Athens"]
    else:
        raise Exception("No direct flight from Naples to Athens")

    # Visit Copenhagen
    if 'Copenhagen' in direct_flights['Athens']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Athens', 'to': 'Copenhagen'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Copenhagen"] - 1}', 'place': 'Copenhagen'})
        visited_cities.add('Copenhagen')
        current_day += city_stay["Copenhagen"]
    else:
        raise Exception("No direct flight from Athens to Copenhagen")

    # Visit Prague
    if 'Prague' in direct_flights['Copenhagen']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Copenhagen', 'to': 'Prague'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Prague"] - 1}', 'place': 'Prague'})
        visited_cities.add('Prague')
        current_day += city_stay["Prague"]
    else:
        raise Exception("No direct flight from Copenhagen to Prague")

    # Visit Geneva
    if 'Geneva' in direct_flights['Prague']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Prague', 'to': 'Geneva'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Geneva"] - 1}', 'place': 'Geneva'})
        visited_cities.add('Geneva')
        current_day += city_stay["Geneva"]
    else:
        raise Exception("No direct flight from Prague to Geneva")

    # Visit Mykonos
    if 'Mykonos' in direct_flights['Geneva']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Geneva', 'to': 'Mykonos'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Mykonos"] - 1}', 'place': 'Mykonos'})
        visited_cities.add('Mykonos')
        current_day += city_stay["Mykonos"]
    else:
        raise Exception("No direct flight from Geneva to Mykonos")

    # Visit Dubrovnik
    if 'Dubrovnik' in direct_flights['Mykonos']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Mykonos', 'to': 'Dubrovnik'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Dubrovnik"] - 1}', 'place': 'Dubrovnik'})
        visited_cities.add('Dubrovnik')
        current_day += city_stay["Dubrovnik"]
    else:
        raise Exception("No direct flight from Mykonos to Dubrovnik")

    # Visit Santorini
    if 'Santorini' in direct_flights['Dubrovnik']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dubrovnik', 'to': 'Santorini'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Santorini"] - 1}', 'place': 'Santorini'})
        visited_cities.add('Santorini')
        current_day += city_stay["Santorini"]
    else:
        raise Exception("No direct flight from Dubrovnik to Santorini")

    # Visit Brussels
    if 'Brussels' in direct_flights['Santorini']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Santorini', 'to': 'Brussels'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Brussels"] - 1}', 'place': 'Brussels'})
        visited_cities.add('Brussels')
        current_day += city_stay["Brussels"]
    else:
        raise Exception("No direct flight from Santorini to Brussels")

    # Visit Munich
    if 'Munich' in direct_flights['Brussels']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Brussels', 'to': 'Munich'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Munich"] - 1}', 'place': 'Munich'})
        visited_cities.add('Munich')
        current_day += city_stay["Munich"]
    else:
        raise Exception("No direct flight from Brussels to Munich")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5
    }

    direct_flights = {
        "Copenhagen": ["Dubrovnik", "Brussels", "Prague", "Munich", "Athens"],
        "Brussels": ["Copenhagen", "Naples", "Munich", "Athens", "Geneva"],
        "Prague": ["Geneva", "Athens", "Copenhagen", "Brussels", "Munich"],
        "Athens": ["Geneva", "Dubrovnik", "Mykonos", "Munich", "Copenhagen", "Brussels", "Naples"],
        "Naples": ["Dubrovnik", "Mykonos", "Munich", "Athens", "Copenhagen", "Geneva", "Brussels"],
        "Munich": ["Mykonos", "Dubrovnik", "Brussels", "Copenhagen", "Athens", "Naples", "Geneva", "Prague"],
        "Geneva": ["Mykonos", "Munich", "Dubrovnik", "Santorini", "Athens", "Copenhagen", "Brussels", "Prague", "Naples"],
        "Mykonos": ["Dubrovnik", "Naples", "Munich", "Athens", "Geneva"],
        "Dubrovnik": ["Munich", "Santorini", "Copenhagen", "Athens", "Naples", "Geneva"],
        "Santorini": ["Geneva", "Athens", "Naples", "Copenhagen", "Brussels"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()