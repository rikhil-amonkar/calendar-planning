import json

def calculate_trip_plan(constraints, direct_flights):
    trip_plan = []
    current_day = 1
    visited_cities = set()
    city_stay = {}

    # Initialize city_stay dictionary
    for city, stay in constraints.items():
        city_stay[city] = stay

    # Visit Venice
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Venice"] - 1}', 'place': 'Venice'})
    visited_cities.add('Venice')
    current_day += city_stay["Venice"]

    # Visit Santorini
    if 'Santorini' in direct_flights['Venice']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Venice', 'to': 'Santorini'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Santorini"] - 1}', 'place': 'Santorini'})
        visited_cities.add('Santorini')
        current_day += city_stay["Santorini"]
    else:
        raise Exception("No direct flight from Venice to Santorini")

    # Visit Manchester
    if 'Manchester' in direct_flights['Santorini']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Santorini', 'to': 'Manchester'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Manchester"] - 1}', 'place': 'Manchester'})
        visited_cities.add('Manchester')
        current_day += city_stay["Manchester"]
    else:
        raise Exception("No direct flight from Santorini to Manchester")

    # Visit Bucharest
    if 'Bucharest' in direct_flights['Manchester']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Manchester', 'to': 'Bucharest'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Bucharest"] - 1}', 'place': 'Bucharest'})
        visited_cities.add('Bucharest')
        current_day += city_stay["Bucharest"]
    else:
        raise Exception("No direct flight from Manchester to Bucharest")

    # Visit Vienna
    if 'Vienna' in direct_flights['Bucharest']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Vienna'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Vienna"] - 1}', 'place': 'Vienna'})
        visited_cities.add('Vienna')
        current_day += city_stay["Vienna"]
    else:
        raise Exception("No direct flight from Bucharest to Vienna")

    # Visit Valencia
    if 'Valencia' in direct_flights['Vienna']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Valencia'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Valencia"] - 1}', 'place': 'Valencia'})
        visited_cities.add('Valencia')
        current_day += city_stay["Valencia"]
    else:
        raise Exception("No direct flight from Vienna to Valencia")

    # Visit Porto
    if 'Porto' in direct_flights['Valencia']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Valencia', 'to': 'Porto'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Porto"] - 1}', 'place': 'Porto'})
        visited_cities.add('Porto')
        current_day += city_stay["Porto"]
    else:
        raise Exception("No direct flight from Valencia to Porto")

    # Visit Munich
    if 'Munich' in direct_flights['Porto']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Porto', 'to': 'Munich'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Munich"] - 1}', 'place': 'Munich'})
        visited_cities.add('Munich')
        current_day += city_stay["Munich"]
    else:
        raise Exception("No direct flight from Porto to Munich")

    # Visit Tallinn
    if 'Tallinn' in direct_flights['Munich']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Munich', 'to': 'Tallinn'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Tallinn"] - 1}', 'place': 'Tallinn'})
        visited_cities.add('Tallinn')
        current_day += city_stay["Tallinn"]
    else:
        raise Exception("No direct flight from Munich to Tallinn")

    # Visit Reykjavik
    if 'Reykjavik' in direct_flights['Vienna']:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Reykjavik'})
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + city_stay["Reykjavik"] - 1}', 'place': 'Reykjavik'})
        visited_cities.add('Reykjavik')
        current_day += city_stay["Reykjavik"]
    else:
        raise Exception("No direct flight from Vienna to Reykjavik")

    # Check if all cities are visited
    for city in constraints:
        if city not in visited_cities:
            raise Exception(f"City {city} is not visited")

    return trip_plan

def main():
    constraints = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }

    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Valencia", "Vienna", "Bucharest"],
        "Santorini": ["Manchester", "Vienna", "Bucharest"],
        "Valencia": ["Vienna", "Porto"],
        "Vienna": ["Reykjavik"],
        "Venice": ["Santorini", "Manchester", "Vienna"],
        "Manchester": ["Vienna"],
        "Porto": ["Vienna", "Manchester"],
        "Tallinn": ["Munich"],
        "Reykjavik": ["Vienna"],
    }

    trip_plan = calculate_trip_plan(constraints, direct_flights)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()