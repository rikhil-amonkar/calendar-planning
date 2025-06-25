import json
from collections import defaultdict
from itertools import chain, combinations

# Define the direct flights between cities
direct_flights = {
    'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva'],
    'Krakow': ['Paris', 'Split', 'Amsterdam', 'Vilnius', 'Munich'],
    'Amsterdam': ['Paris', 'Split', 'Geneva', 'Vilnius', 'Munich', 'Budapest'],
    'Split': ['Paris', 'Krakow', 'Amsterdam', 'Geneva', 'Munich'],
    'Geneva': ['Paris', 'Amsterdam', 'Munich', 'Budapest', 'Santorini'],
    'Munich': ['Vilnius', 'Amsterdam', 'Split', 'Geneva', 'Krakow', 'Budapest'],
    'Vilnius': ['Munich', 'Paris', 'Amsterdam', 'Split', 'Krakow'],
    'Budapest': ['Amsterdam', 'Geneva', 'Munich', 'Paris'],
    'Santorini': ['Geneva']
}

# Define the constraints
constraints = {
    'Santorini': [25, 29],
    'Krakow': [18, 22],
    'Paris': [11, 15]
}

# Define the city durations
city_durations = {
    'Santorini': 5,
    'Krakow': 5,
    'Paris': 5,
    'Vilnius': 3,
    'Munich': 5,
    'Geneva': 2,
    'Amsterdam': 4,
    'Budapest': 5,
    'Split': 4
}

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def calculate_itinerary(city_durations, direct_flights, constraints):
    max_days = 30
    optimal_itinerary = None

    for r in powerset(city_durations.keys()):
        if len(r) == 0:
            continue

        days_in_cities = {city: 0 for city in city_durations.keys()}
        days_in_cities.update({city: city_durations[city] for city in r})

        total_days = sum(days_in_cities.values())
        if total_days!= max_days:
            continue

        itinerary = []
        current_day = 1
        current_city = None

        for city in r:
            days_in_city = days_in_cities[city]
            itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_city - 1}', 'place': city})
            current_day += days_in_city

            for i in range(days_in_city):
                if city in constraints and constraints[city][0] <= current_day <= constraints[city][1]:
                    itinerary.append({'day_range': f'Day {current_day}', 'place': city})

                if i < days_in_city - 1:
                    next_city = None
                    for next_city in direct_flights[city]:
                        if next_city not in r:
                            break
                    if next_city is None:
                        continue
                    current_day += 1

        # Check if the itinerary covers exactly 30 days
        if len(itinerary) == max_days:
            if optimal_itinerary is None or len(itinerary) < len(optimal_itinerary):
                optimal_itinerary = itinerary

    return optimal_itinerary

def main():
    optimal_itinerary = calculate_itinerary(city_durations, direct_flights, constraints)
    if optimal_itinerary is not None:
        output = {'itinerary': optimal_itinerary}
        print(json.dumps(output, indent=4))
    else:
        # Changed the message to be more informative
        print(json.dumps({'itinerary': 'No valid itinerary found. Please check the constraints and city durations.'}, indent=4))

if __name__ == "__main__":
    main()