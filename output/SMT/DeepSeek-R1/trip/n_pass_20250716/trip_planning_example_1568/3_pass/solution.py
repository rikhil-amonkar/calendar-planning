def main():
    previous_output = {
        "itinerary": [
            {"day_range": "Day 1-5", "place": "Vienna"},
            {"day_range": "Day 5-9", "place": "Prague"},
            {"day_range": "Day 5", "place": "Vienna"},
            {"day_range": "Day 5", "place": "Prague"},
            {"day_range": "Day 9-10", "place": "Istanbul"},
            {"day_range": "Day 9", "place": "Prague"},
            {"day_range": "Day 9", "place": "Istanbul"},
            {"day_range": "Day 10-11", "place": "Munich"},
            {"day_range": "Day 10", "place": "Istanbul"},
            {"day_range": "Day 10", "place": "Munich"},
            {"day_range": "Day 11-13", "place": "Split"},
            {"day_range": "Day 11", "place": "Munich"},
            {"day_range": "Day 11", "place": "Split"},
            {"day_range": "Day 13-15", "place": "Amsterdam"},
            {"day_range": "Day 13", "place": "Split"},
            {"day_range": "Day 13", "place": "Amsterdam"},
            {"day_range": "Day 15-16", "place": "Riga"},
            {"day_range": "Day 15", "place": "Amsterdam"},
            {"day_range": "Day 15", "place": "Riga"},
            {"day_range": "Day 16-17", "place": "Stockholm"},
            {"day_range": "Day 16", "place": "Riga"},
            {"day_range": "Day 16", "place": "Stockholm"},
            {"day_range": "Day 17-18", "place": "Brussels"},
            {"day_range": "Day 17", "place": "Stockholm"},
            {"day_range": "Day 17", "place": "Brussels"},
            {"day_range": "Day 18-20", "place": "Seville"},
            {"day_range": "Day 18", "place": "Brussels"},
            {"day_range": "Day 18", "place": "Seville"}
        ]
    }

    # Filter only continuous range entries (with hyphen)
    continuous_entries = []
    for entry in previous_output['itinerary']:
        if '-' in entry['day_range']:
            continuous_entries.append(entry)
            
    # Parse day range string into start and end integers
    def parse_range(day_range_str):
        parts = day_range_str.replace('Day ', '').split('-')
        start = int(parts[0])
        end = int(parts[1]) if len(parts) > 1 else start
        return start, end

    # Adjust end days to avoid overlaps
    adjusted_entries = []
    for i in range(len(continuous_entries)):
        start, end = parse_range(continuous_entries[i]['day_range'])
        # For all except last entry, end one day before next starts
        if i < len(continuous_entries) - 1:
            next_start, _ = parse_range(continuous_entries[i+1]['day_range'])
            if end >= next_start:
                end = next_start - 1
        adjusted_entries.append({
            'place': continuous_entries[i]['place'],
            'start': start,
            'end': end
        })
    
    # Format adjusted entries into final itinerary
    result_itinerary = []
    for adj in adjusted_entries:
        start = adj['start']
        end = adj['end']
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        result_itinerary.append({
            'day_range': day_range_str,
            'place': adj['place']
        })
    
    # Verify total days = 20
    total_days = 0
    for entry in result_itinerary:
        parts = entry['day_range'].replace('Day ', '').split('-')
        start = int(parts[0])
        end = int(parts[1]) if len(parts) > 1 else start
        total_days += (end - start + 1)
    
    if total_days != 20:
        # Fallback: Use original continuous entries if adjustment fails
        result_itinerary = []
        for entry in continuous_entries:
            start, end = parse_range(entry['day_range'])
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            result_itinerary.append({
                'day_range': day_range_str,
                'place': entry['place']
            })
    
    corrected = {'itinerary': result_itinerary}
    print(corrected)

if __name__ == "__main__":
    main()