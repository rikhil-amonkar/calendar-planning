import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Attend conference in Reykjavik
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Reykjavik"] - 1}', 'place': 'Reykjavik'})
    visited_cities.add('Reykjavik')
    current_day += city_stay["Reykjavik"]

    # Meet a friend in Stockholm
    if 'Stockholm' in direct_flights['Reykjavik']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Stockholm'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Stockholm"] - 1}', 'place': 'Stockholm'})
        visited_cities.add('Stockholm')
        current_day += city_stay["Stockholm"]
    else:
        raise Exception("No direct flight from Reykjavik to Stockholm")

    # Visit Oslo
    if 'Oslo' in direct_flights['Stockholm']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stockholm', 'to': 'Oslo'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Oslo"] - 1}', 'place': 'Oslo'})
        visited_cities.add('Oslo')
        current_day += city_stay["Oslo"]
    else:
        raise Exception("No direct flight from Stockholm to Oslo")

    # Visit Geneva
    if 'Geneva' in direct_flights['Oslo']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Geneva'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Geneva"] - 1}', 'place': 'Geneva'})
        visited_cities.add('Geneva')
        current_day += city_stay["Geneva"]
    else:
        raise Exception("No direct flight from Oslo to Geneva")

    # Visit Porto
    if 'Porto' in direct_flights['Geneva']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Geneva', 'to': 'Porto'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Porto"] - 1}', 'place': 'Porto'})
        visited_cities.add('Porto')
        current_day += city_stay["Porto"]
    else:
        raise Exception("No direct flight from Geneva to Porto")

    # Visit Split
    if 'Split' in direct_flights['Geneva']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Geneva', 'to': 'Split'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Split"] - 1}', 'place': 'Split'})
        visited_cities.add('Split')
        current_day += city_stay["Split"]
    else:
        raise Exception("No direct flight from Geneva to Split")

    # Visit Stuttgart
    if 'Stuttgart' in direct_flights['Split']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Stuttgart'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Stuttgart"] - 1}', 'place': 'Stuttgart'})
        visited_cities.add('Stuttgart')
        current_day += city_stay["Stuttgart"]
    else:
        raise Exception("No direct flight from Split to Stuttgart")

    # Visit Tallinn
    if 'Tallinn' in direct_flights['Oslo']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Tallinn'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Tallinn"] - 1}', 'place': 'Tallinn'})
        visited_cities.add('Tallinn')
        current_day += city_stay["Tallinn"]
    else:
        raise Exception("No direct flight from Oslo to Tallinn")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3
    }

    direct_flights = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Stuttgart", "Oslo", "Reykjavik", "Split", "Geneva"],
        "Oslo": ["Split", "Geneva", "Porto", "Reykjavik", "Tallinn"],
        "Stuttgart": ["Porto", "Split", "Reykjavik"],
        "Split": ["Stuttgart", "Geneva", "Oslo"],
        "Geneva": ["Porto", "Split", "Oslo", "Stockholm"],
        "Porto": ["Geneva", "Oslo"],
        "Tallinn": ["Oslo"],
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()