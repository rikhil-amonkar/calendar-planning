import json

def plan_trip():
    total_days = 12
    # More flexible day distribution
    dublin_days = 2
    riga_days = 6  # Increased from 5 to better utilize connections
    vilnius_days = 4  # Adjusted to maintain total days

    # Validate total days
    if riga_days + vilnius_days + dublin_days != total_days:
        raise ValueError(f"Total days do not sum up to 12 (sum={riga_days + vilnius_days + dublin_days})")

    # Flight connections (more comprehensive validation)
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

    # Dublin
    itinerary.append({
        "day_range": f"Day {current_day}-{current_day + dublin_days - 1}",
        "place": "Dublin"
    })
    current_day += dublin_days

    # Riga
    itinerary.append({
        "day_range": f"Day {current_day}-{current_day + riga_days - 1}",
        "place": "Riga"
    })
    current_day += riga_days

    # Vilnius
    itinerary.append({
        "day_range": f"Day {current_day}-{current_day + vilnius_days - 1}",
        "place": "Vilnius"
    })

    return {"itinerary": itinerary}

result = plan_trip()
print(json.dumps(result, indent=2))