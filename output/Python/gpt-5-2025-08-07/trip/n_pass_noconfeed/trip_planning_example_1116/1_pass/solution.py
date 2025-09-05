import json
import itertools

def main():
    # Input variables (constraints)
    total_days = 20

    durations = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3,
    }

    # Direct flights (bidirectional)
    direct_pairs = [
        ("Reykjavik", "Munich"),
        ("Munich", "Frankfurt"),
        ("Split", "Oslo"),
        ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"),
        ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"),
        ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Reykjavik"),
        ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"),
        ("Bucharest", "Oslo"),
        ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"),
        ("Barcelona", "Oslo"),
        ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"),
        ("Split", "Frankfurt"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"),
        ("Munich", "Oslo"),
        ("Split", "Munich"),
    ]

    direct_flights = set()
    for a, b in direct_pairs:
        direct_flights.add((a, b))
        direct_flights.add((b, a))

    def has_direct(a, b):
        return (a, b) in direct_flights

    # Time windows (inclusive)
    show_in_oslo = (16, 17)         # must be in Oslo both days
    meet_in_reykjavik = (9, 13)     # Reykjavik presence during this window
    relatives_in_munich = (13, 16)  # Munich presence during this window
    workshop_in_frankfurt = (17, 20)  # Frankfurt presence throughout

    # Build anchored segments from hard windows (their durations match the windows)
    segments = {}

    # Oslo: exact 2 days, fixed by show
    oslo_start, oslo_end = show_in_oslo
    assert durations["Oslo"] == (oslo_end - oslo_start + 1)
    segments["Oslo"] = (oslo_start, oslo_end)

    # Frankfurt: exact 4 days, fixed by workshop
    fra_start, fra_end = workshop_in_frankfurt
    assert durations["Frankfurt"] == (fra_end - fra_start + 1)
    segments["Frankfurt"] = (fra_start, fra_end)
    # Ensure direct flight Oslo->Frankfurt
    assert has_direct("Oslo", "Frankfurt")

    # Munich: exact window 13-16 (4 days)
    muc_start, muc_end = relatives_in_munich
    assert durations["Munich"] == (muc_end - muc_start + 1)
    segments["Munich"] = (muc_start, muc_end)
    # Ensure direct flight Munich->Oslo with overlap on day 16
    assert muc_end == oslo_start and has_direct("Munich", "Oslo")

    # Reykjavik: exact window 9-13 (5 days)
    rkv_start, rkv_end = meet_in_reykjavik
    assert durations["Reykjavik"] == (rkv_end - rkv_start + 1)
    segments["Reykjavik"] = (rkv_start, rkv_end)
    # Ensure direct flight Reykjavik->Munich with overlap on day 13
    assert rkv_end == muc_start and has_direct("Reykjavik", "Munich")

    # Stockholm: 4 days, place it to end exactly when Reykjavik starts (overlap at day 9)
    sto_end = rkv_start
    sto_start = sto_end - durations["Stockholm"] + 1
    segments["Stockholm"] = (sto_start, sto_end)
    # Ensure direct flight Stockholm->Reykjavik with overlap at day 9
    assert has_direct("Stockholm", "Reykjavik")

    # Remaining cities to place before Stockholm starts
    remaining = ["Barcelona", "Bucharest", "Split"]
    target_end_before_stockholm = sto_start  # day 6 in this setup

    # Find an order that respects direct flights and ends with a city that connects to Stockholm
    valid_order = None
    for order in itertools.permutations(remaining):
        if all(has_direct(order[i], order[i+1]) for i in range(len(order)-1)) and has_direct(order[-1], "Stockholm"):
            valid_order = order
            break

    if not valid_order:
        raise RuntimeError("No valid ordering found for the remaining cities with direct flights to Stockholm.")

    # Assign day ranges for the remaining cities starting from Day 1 sequentially
    current_start = 1
    for city in valid_order:
        length = durations[city]
        start = current_start
        end = start + length - 1
        segments[city] = (start, end)
        current_start = end  # overlap next city's start with this end

    # Verify the chain aligns to Stockholm's start
    last_of_remaining = valid_order[-1]
    assert segments[last_of_remaining][1] == target_end_before_stockholm

    # Construct full order by start day
    full_order = sorted(segments.items(), key=lambda kv: kv[1][0])

    # Validate day coverage and flight connections
    # - Unique days covered should be 1..20
    min_day = min(s for _, (s, e) in full_order)
    max_day = max(e for _, (s, e) in full_order)
    assert min_day == 1 and max_day == total_days

    # - Check direct flights between consecutive segments
    for (city_a, (sa, ea)), (city_b, (sb, eb)) in zip(full_order[:-1], full_order[1:]):
        assert ea == sb, f"Segments must overlap exactly on transition day: {city_a} -> {city_b}"
        assert has_direct(city_a, city_b), f"No direct flight between {city_a} and {city_b}"

    # - Validate durations
    for city, (s, e) in segments.items():
        assert durations[city] == (e - s + 1), f"Duration mismatch for {city}"

    # - Validate windows are covered
    def covers(city, win):
        s, e = segments[city]
        return s <= win[0] and e >= win[1]

    assert covers("Oslo", show_in_oslo)
    assert covers("Frankfurt", workshop_in_frankfurt)
    assert covers("Munich", relatives_in_munich)
    assert covers("Reykjavik", meet_in_reykjavik)

    # Prepare JSON itinerary output
    itinerary = []
    for city, (s, e) in full_order:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()