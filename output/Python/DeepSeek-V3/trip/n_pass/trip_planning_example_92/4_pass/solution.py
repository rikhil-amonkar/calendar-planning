import json

def plan_trip(total_days=12):
    # Validate total days
    if not isinstance(total_days, int) or total_days <= 0:
        raise ValueError("Total days must be a positive integer")

    # Day distribution with validation
    day_distribution = {
        "Dublin": 2,
        "Riga": 6,
        "Vilnius": 4
    }

    # Verify days sum to total
    if sum(day_distribution.values()) != total_days:
        raise ValueError(f"Day distribution must sum to {total_days}")

    # Flight connections graph
    connections = {
        "Dublin": ["Riga"],
        "Riga": ["Vilnius", "Dublin"],
        "Vilnius": ["Riga"]
    }

    # Validate itinerary sequence is possible with connections
    def is_valid_sequence(sequence):
        for i in range(len(sequence)-1):
            current = sequence[i]
            next_city = sequence[i+1]
            if next_city not in connections.get(current, []):
                return False
        return True

    # Proposed itinerary sequence
    sequence = ["Dublin", "Riga", "Vilnius"]
    if not is_valid_sequence(sequence):
        raise ValueError("Invalid itinerary sequence based on flight connections")

    # Build itinerary
    itinerary = []
    current_day = 1

    for city, days in day_distribution.items():
        end_day = current_day + days - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day += days

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, indent=2))