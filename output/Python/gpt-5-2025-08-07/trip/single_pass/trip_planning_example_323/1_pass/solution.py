import json
from typing import List, Dict, Tuple, Optional, Set

def main():
    # Input variables (constraints)
    total_days = 16
    cities = ["London", "Split", "Oslo", "Porto"]
    durations = {
        "London": 7,
        "Split": 5,
        "Oslo": 2,
        "Porto": 5
    }
    # Fixed windows (inclusive)
    split_show_window = (7, 11)  # Must be in Split from day 7 to 11
    london_relatives_window = (1, 7)  # Visit relatives between days 1 and 7
    
    # Direct flights (undirected)
    direct_flights = {
        frozenset(["London", "Oslo"]),
        frozenset(["Split", "Oslo"]),
        frozenset(["Oslo", "Porto"]),
        frozenset(["London", "Split"]),
    }
    
    def has_direct(a: str, b: str) -> bool:
        return frozenset([a, b]) in direct_flights

    # Determine order algorithmically
    # 1) Split is fixed to days 7-11; therefore, the previous city's last day must be 7.
    # 2) To end a block on day 7 with start on day 1, the previous city's duration must be 7 (London),
    #    and it must lie within the relatives window. So London must be first, occupying days 1-7.
    # 3) Split must follow London, starting on day 7 (direct flight exists).
    # 4) Remaining cities must form a path from Split using only direct flights.
    
    fixed_prefix = ["London", "Split"]
    remaining = [c for c in cities if c not in fixed_prefix]
    
    # DFS to find a feasible order for remaining cities such that each consecutive pair has a direct flight
    def find_path_from(current: str, remaining_set: Set[str]) -> Optional[List[str]]:
        if not remaining_set:
            return []
        for nxt in list(remaining_set):
            if has_direct(current, nxt):
                new_remaining = set(remaining_set)
                new_remaining.remove(nxt)
                tail = find_path_from(nxt, new_remaining)
                if tail is not None:
                    return [nxt] + tail
        return None
    
    remaining_order = find_path_from(fixed_prefix[-1], set(remaining))
    if remaining_order is None:
        raise ValueError("No valid path using only direct flights to visit all cities.")
    
    order = fixed_prefix + remaining_order
    
    # Compute the schedule with overlaps on flight days
    # Rule: If flying from A to B on day X, day X counts for both A and B.
    # Implementation: start_1 = 1; end_i = start_i + dur_i - 1; start_(i+1) = end_i
    segments: List[Tuple[str, int, int]] = []
    start_day = 1
    for idx, city in enumerate(order):
        dur = durations[city]
        end_day = start_day + dur - 1
        segments.append((city, start_day, end_day))
        start_day = end_day  # Next city starts on the same end day (overlap)
    
    # Validation
    # 1) Total unique days equals last end day and must equal total_days
    last_end_day = segments[-1][2]
    if last_end_day != total_days:
        raise ValueError(f"Computed schedule does not span exactly {total_days} days; got {last_end_day} days.")
    
    # 2) Each city's allocated days must match required durations
    for city, s, e in segments:
        if e - s + 1 != durations[city]:
            raise ValueError(f"Duration mismatch for {city}: expected {durations[city]}, got {e - s + 1}.")
    
    # 3) Direct flights between consecutive cities
    for i in range(len(segments) - 1):
        a = segments[i][0]
        b = segments[i + 1][0]
        if not has_direct(a, b):
            raise ValueError(f"No direct flight between {a} and {b}.")
    
    # 4) Split must be exactly on days 7-11
    split_seg = next((seg for seg in segments if seg[0] == "Split"), None)
    if split_seg is None or (split_seg[1], split_seg[2]) != split_show_window:
        raise ValueError(f"Split must be scheduled exactly from day {split_show_window[0]} to {split_show_window[1]}, got {split_seg}.")
    
    # 5) London must be scheduled within relatives window, and for 7 days
    london_seg = next((seg for seg in segments if seg[0] == "London"), None)
    if not (london_relatives_window[0] <= london_seg[1] and london_seg[2] <= london_relatives_window[1]):
        raise ValueError(f"London must be within days {london_relatives_window}, got {london_seg[1]}-{london_seg[2]}.")
    
    # Prepare output itinerary
    itinerary = []
    for city, s, e in segments:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
    
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()