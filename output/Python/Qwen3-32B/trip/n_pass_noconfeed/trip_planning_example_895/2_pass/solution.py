import itertools
import json

def main():
    cities = ["Brussels", "Lisbon", "Venice", "Madrid", "London", "Reykjavik", "Santorini"]
    required_days = {
        "Brussels": 2,
        "Lisbon": 4,
        "Venice": 3,
        "Madrid": 5,
        "London": 3,
        "Reykjavik": 3,
        "Santorini": 3,
    }
    direct_flights = {
        ("Brussels", "Venice"),
        ("Brussels", "London"),
        ("Brussels", "Lisbon"),
        ("Brussels", "Reykjavik"),
        ("Brussels", "Madrid"),
        ("Venice", "Madrid"),
        ("Venice", "Santorini"),
        ("Venice", "Lisbon"),
        ("Venice", "London"),
        ("Lisbon", "Reykjavik"),
        ("Lisbon", "Venice"),
        ("Lisbon", "London"),
        ("Lisbon", "Madrid"),
        ("Reykjavik", "Lisbon"),
        ("Reykjavik", "London"),
        ("Reykjavik", "Madrid"),
        ("London", "Brussels"),
        ("London", "Madrid"),
        ("London", "Santorini"),
        ("London", "Reykjavik"),
        ("Madrid", "Brussels"),
        ("Madrid", "Reykjavik"),
        ("Madrid", "Lisbon"),
        ("Madrid", "Santorini"),
        ("Santorini", "Venice"),
        ("Santorini", "Madrid"),
        ("Santorini", "London"),
        # Ensure bidirectional flights
        ("Venice", "Brussels"),
        ("London", "Brussels"),
        ("Lisbon", "Brussels"),
        ("Reykjavik", "Brussels"),
        ("Madrid", "Brussels"),
        ("Madrid", "Venice"),
        ("Santorini", "Venice"),
        ("Lisbon", "Venice"),
        ("London", "Venice"),
        ("Reykjavik", "Lisbon"),
        ("Venice", "Lisbon"),
        ("London", "Lisbon"),
        ("Madrid", "Lisbon"),
        ("Lisbon", "Madrid"),
        ("London", "Reykjavik"),
        ("Madrid", "Reykjavik"),
        ("Reykjavik", "Madrid"),
        ("Madrid", "Santorini"),
        ("Santorini", "Madrid"),
        ("London", "Santorini"),
        ("Santorini", "London"),  # Added missing reverse flight
    }

    remaining_cities = [city for city in cities if city != "Brussels"]
    for perm in itertools.permutations(remaining_cities):
        sequence = ["Brussels"] + list(perm)
        valid_transitions = True
        for i in range(len(sequence) - 1):
            city_a = sequence[i]
            city_b = sequence[i + 1]
            if (city_a, city_b) not in direct_flights:
                valid_transitions = False
                break
        if not valid_transitions:
            continue

        day_ranges = []
        current_start = 1
        duration = required_days["Brussels"]
        current_end = current_start + duration - 1
        day_ranges.append((current_start, current_end, "Brussels"))
        for city in sequence[1:]:
            current_start = current_end + 1
            duration = required_days[city]
            current_end = current_start + duration - 1
            day_ranges.append((current_start, current_end, city))

        if current_end != 23:  # Total required days is 23
            continue

        venice_in_range = False
        madrid_in_range = False
        for start, end, city in day_ranges:
            if city == "Venice":
                if not (end < 5 or start > 7):
                    venice_in_range = True
            if city == "Madrid":
                if not (end < 7 or start > 11):
                    madrid_in_range = True

        if not venice_in_range and not madrid_in_range:  # Valid only if both are NOT in forbidden ranges
            itinerary = []
            for start, end, city in day_ranges:
                day_range_str = f"Day {start}-{end}"  # Corrected day range
                itinerary.append({"day_range": day_range_str, "place": city})
            print(json.dumps({"itinerary": itinerary}))
            return

if __name__ == "__main__":
    main()