import json

def main():
    # Represent the itinerary segments as tuples (start_day, end_day, place)
    segments = [
        (1, 1, "Helsinki"),
        (2, 3, "Zurich"),
        (4, 8, "Split"),
        (9, 9, "Split"),
        (10, 10, "Hamburg"),
        (11, 12, "Helsinki")
    ]
    
    # Merge consecutive segments with the same place
    merged_segments = []
    current_start, current_end, current_place = segments[0]
    
    for seg in segments[1:]:
        start, end, place = seg
        if place == current_place and start == current_end + 1:
            # Extend the current segment
            current_end = end
        else:
            # Save current segment and start new
            merged_segments.append((current_start, current_end, current_place))
            current_start, current_end, current_place = start, end, place
    
    # Append the last segment
    merged_segments.append((current_start, current_end, current_place))
    
    # Convert to output format
    itinerary = []
    for seg in merged_segments:
        start, end, place = seg
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start} to Day {end}"
        itinerary.append({"day_range": day_range, "place": place})
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()