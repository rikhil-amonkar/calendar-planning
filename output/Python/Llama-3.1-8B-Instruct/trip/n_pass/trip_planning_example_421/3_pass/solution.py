import json
from collections import defaultdict

def compute_itinerary(cities, durations, transitions, total_days):
    """
    Compute an itinerary for a given set of cities, durations, and transitions.

    Args:
        cities (list): A list of city names.
        durations (dict): A dictionary mapping city names to their durations.
        transitions (list): A list of city pairs representing transitions.
        total_days (int): The total number of days for the itinerary.

    Returns:
        dict: An itinerary with day ranges and city names.
    """
    # Validate input data
    if not isinstance(cities, list) or not all(isinstance(city, str) for city in cities):
        raise ValueError("Cities must be a list of strings")
    if not isinstance(durations, dict) or not all(isinstance(duration, int) and duration >= 0 for duration in durations.values()):
        raise ValueError("Durations must be a dictionary with non-negative integer values")
    if not isinstance(transitions, list) or not all(isinstance(transition, tuple) and len(transition) == 2 for transition in transitions):
        raise ValueError("Transitions must be a list of city pairs")
    if not isinstance(total_days, int) or total_days <= 0:
        raise ValueError("Total days must be a positive integer")

    # Create a graph of city transitions
    graph = defaultdict(list)
    for start, end in transitions:
        if start not in cities or end not in cities:
            raise ValueError(f"Invalid transition: ({start}, {end})")
        graph[start].append(end)

    # Initialize the itinerary and current city
    itinerary = []
    current_city = None
    days = 0

    # Iterate through the days
    while days < total_days:
        # Find a city to visit
        for city, duration in durations.items():
            if duration > 0:
                if days + duration <= total_days:
                    current_city = city
                    # Add the city to the itinerary
                    itinerary.append({"day_range": f"Day {days + 1}-{days + duration}" if duration > 1 else f"Day {days + 1}", "place": city})
                    # Update the duration and days
                    durations[city] = 0
                    days += duration
                    break

        # If we can't find a city to visit, stay in the current city
        if days < total_days:
            # Find a city to transition to
            next_cities = graph[current_city]
            if next_cities:
                next_city = next_cities[0]
                if durations[next_city] > 0:
                    current_city = next_city
            else:
                # If we can't find a city to transition to, stay in the current city
                durations[current_city] = 0

    return {"itinerary": itinerary}

def main():
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    durations = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }
    transitions = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin")
    ]
    total_days = 20

    result = compute_itinerary(cities, durations, transitions, total_days)
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()