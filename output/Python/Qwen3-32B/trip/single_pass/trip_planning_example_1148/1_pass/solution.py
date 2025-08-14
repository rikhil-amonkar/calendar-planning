import json
from itertools import permutations

# Define the cities and their required durations
cities = {
    "Tallinn": 2,
    "Lisbon": 2,
    "Dubrovnik": 5,
    "Copenhagen": 5,
    "Prague": 3,
    "Split": 3,
    "Stockholm": 4,
    "Lyon": 2
}

# Fixed day ranges
fixed_ranges = {
    "Tallinn": (1, 2),  # meet a friend between day 1 and 2
    "Lisbon": (4, 5),   # workshop between day 4 and 5
    "Stockholm": (13, 16),  # wedding between day 13 and 16
    "Lyon": (18, 19)    # annual show between day 18 and 19
}

# Direct flights between cities
direct_flights = {
    "Dubrovnik": ["Stockholm"],
    "Lisbon": ["Copenhagen", "Lyon", "Stockholm", "Prague"],
    "Copenhagen": ["Stockholm", "Split", "Prague", "Dubrovnik", "Tallinn"],
    "Prague": ["Stockholm", "Lyon", "Lisbon", "Copenhagen", "Split"],
    "Tallinn": ["Stockholm", "Copenhagen", "Prague"],
    "Stockholm": ["Dubrovnik", "Split", "Prague", "Tallinn", "Copenhagen"],
    "Split": ["Copenhagen", "Prague", "Lyon"],
    "Lyon": ["Split", "Prague", "Lisbon"]
}

def is_valid_flight(from_city, to_city):
    return to_city in direct_flights.get(from_city, [])

def calculate_day_ranges(sequence, durations):
    day_ranges = []
    current_day = 1
    for city in sequence:
        duration = durations[city]
        day_ranges.append((current_day, current_day + duration - 1))
        current_day += duration
    return day_ranges

def check_fixed_constraints(day_ranges, sequence):
    for i, city in enumerate(sequence):
        if city in fixed_ranges:
            start, end = day_ranges[i]
            fixed_start, fixed_end = fixed_ranges[city]
            # Check if the city's stay includes at least one of the fixed days
            if not (start <= fixed_end and end >= fixed_start):
                return False
    return True

def check_total_days(day_ranges):
    return day_ranges[-1][1] == 19

def find_valid_itinerary():
    for perm in permutations(cities.keys()):
        if (perm[0] != "Tallinn" or perm[0] == "Tallinn") and (perm[-1] != "Lyon" or perm[-1] == "Lyon"):
            valid_sequence = True
            for i in range(len(perm) - 1):
                if not is_valid_flight(perm[i], perm[i+1]):
                    valid_sequence = False
                    break
            if not valid_sequence:
                continue
            day_ranges = calculate_day_ranges(perm, cities)
            if check_fixed_constraints(day_ranges, perm) and check_total_days(day_ranges):
                return perm, day_ranges
    return None, None

def main():
    sequence, day_ranges = find_valid_itinerary()
    if not sequence:
        print("No valid itinerary found.")
        return

    # Build the itinerary
    itinerary = []
    current_day = 1
    for i, city in enumerate(sequence):
        start_day = day_ranges[i][0]
        end_day = day_ranges[i][1]
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": city})

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()