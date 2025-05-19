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

    # Visit Stockholm
    if 'Stockholm' in direct_flights['Reykjavik']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Stockholm'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Stockholm"] - 1}', 'place': 'Stockholm'})
        visited_cities.add('Stockholm')
        current_day += city_stay["Stockholm"]
    else:
        raise Exception("No direct flight from Reykjavik to Stockholm")

    # Visit Munich
    if 'Munich' in direct_flights['Stockholm']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stockholm', 'to': 'Munich'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Munich"] - 1}', 'place': 'Munich'})
        visited_cities.add('Munich')
        current_day += city_stay["Munich"]
    else:
        raise Exception("No direct flight from Stockholm to Munich")

    # Visit Bucharest
    if 'Bucharest' in direct_flights['Munich']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Munich', 'to': 'Bucharest'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Bucharest"] - 1}', 'place': 'Bucharest'})
        visited_cities.add('Bucharest')
        current_day += city_stay["Bucharest"]
    else:
        raise Exception("No direct flight from Munich to Bucharest")

    # Visit Barcelona
    if 'Barcelona' in direct_flights['Bucharest']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Barcelona'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Barcelona"] - 1}', 'place': 'Barcelona'})
        visited_cities.add('Barcelona')
        current_day += city_stay["Barcelona"]
    else:
        raise Exception("No direct flight from Bucharest to Barcelona")

    # Visit Split
    if 'Split' in direct_flights['Barcelona']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Barcelona', 'to': 'Split'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Split"] - 1}', 'place': 'Split'})
        visited_cities.add('Split')
        current_day += city_stay["Split"]
    else:
        raise Exception("No direct flight from Barcelona to Split")

    # Visit Oslo
    if 'Oslo' in direct_flights['Split']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Oslo'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Oslo"] - 1}', 'place': 'Oslo'})
        visited_cities.add('Oslo')
        current_day += city_stay["Oslo"]
    else:
        raise Exception("No direct flight from Split to Oslo")

    # Visit Frankfurt
    if 'Frankfurt' in direct_flights['Oslo']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Frankfurt'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Frankfurt"] - 1}', 'place': 'Frankfurt'})
        visited_cities.add('Frankfurt')
        current_day += city_stay["Frankfurt"]
    else:
        raise Exception("No direct flight from Oslo to Frankfurt")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3
    }

    direct_flights = {
        "Reykjavik": ["Munich", "Oslo", "Frankfurt"],
        "Munich": ["Frankfurt", "Oslo"],
        "Split": ["Oslo", "Stockholm"],
        "Oslo": ["Frankfurt"],
        "Bucharest": ["Munich", "Barcelona", "Oslo", "Frankfurt"],
        "Barcelona": ["Frankfurt", "Stockholm", "Reykjavik", "Oslo", "Munich", "Split"],
        "Stockholm": ["Reykjavik", "Munich", "Oslo", "Frankfurt", "Split"],
        "Frankfurt": ["Munich", "Oslo", "Barcelona", "Stockholm", "Split", "Reykjavik"]
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()