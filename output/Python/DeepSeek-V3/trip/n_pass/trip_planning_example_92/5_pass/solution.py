import json

def plan_trip(total_days=12, city_sequence=None, day_distribution=None):
    # Validate total days
    if not isinstance(total_days, int) or total_days <= 0:
        raise ValueError("Total days must be a positive integer")

    # Default day distribution with validation
    if day_distribution is None:
        day_distribution = {
            "Dublin": 2,
            "Riga": 6,
            "Vilnius": 4
        }
    else:
        # Validate custom day distribution
        if not isinstance(day_distribution, dict):
            raise ValueError("Day distribution must be a dictionary")
        if any(not isinstance(days, int) or days <= 0 for days in day_distribution.values()):
            raise ValueError("All days must be positive integers")

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

    # Determine city sequence
    if city_sequence is None:
        city_sequence = ["Dublin", "Riga", "Vilnius"]
    else:
        if not isinstance(city_sequence, list) or len(city_sequence) == 0:
            raise ValueError("City sequence must be a non-empty list")
        if not all(city in day_distribution for city in city_sequence):
            raise ValueError("All cities in sequence must be in day distribution")
        if len(city_sequence) != len(day_distribution):
            raise ValueError("City sequence must include all cities from day distribution")

    if not is_valid_sequence(city_sequence):
        raise ValueError("Invalid itinerary sequence based on flight connections")

    # Build itinerary
    itinerary = []
    current_day = 1

    for city in city_sequence:
        days = day_distribution[city]
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