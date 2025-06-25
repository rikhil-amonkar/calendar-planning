def main():
    # Given the previous output as a dictionary
    previous_output = {
        "itinerary": [
            {
                "day_range": "Day 1-5",
                "place": "Vienna"
            },
            {
                "day_range": "Day 5-9",
                "place": "Prague"
            },
            {
                "day_range": "Day 5",
                "place": "Vienna"
            },
            {
                "day_range": "Day 5",
                "place": "Prague"
            },
            {
                "day_range": "Day 9-10",
                "place": "Istanbul"
            },
            {
                "day_range": "Day 9",
                "place": "Prague"
            },
            {
                "day_range": "Day 9",
                "place": "Istanbul"
            },
            {
                "day_range": "Day 10-11",
                "place": "Munich"
            },
            {
                "day_range": "Day 10",
                "place": "Istanbul"
            },
            {
                "day_range": "Day 10",
                "place": "Munich"
            },
            {
                "day_range": "Day 11-13",
                "place": "Split"
            },
            {
                "day_range": "Day 11",
                "place": "Munich"
            },
            {
                "day_range": "Day 11",
                "place": "Split"
            },
            {
                "day_range": "Day 13-15",
                "place": "Amsterdam"
            },
            {
                "day_range": "Day 13",
                "place": "Split"
            },
            {
                "day_range": "Day 13",
                "place": "Amsterdam"
            },
            {
                "day_range": "Day 15-16",
                "place": "Riga"
            },
            {
                "day_range": "Day 15",
                "place": "Amsterdam"
            },
            {
                "day_range": "Day 15",
                "place": "Riga"
            },
            {
                "day_range": "Day 16-17",
                "place": "Stockholm"
            },
            {
                "day_range": "Day 16",
                "place": "Riga"
            },
            {
                "day_range": "Day 16",
                "place": "Stockholm"
            },
            {
                "day_range": "Day 17-18",
                "place": "Brussels"
            },
            {
                "day_range": "Day 17",
                "place": "Stockholm"
            },
            {
                "day_range": "Day 17",
                "place": "Brussels"
            },
            {
                "day_range": "Day 18-20",
                "place": "Seville"
            },
            {
                "day_range": "Day 18",
                "place": "Brussels"
            },
            {
                "day_range": "Day 18",
                "place": "Seville"
            }
        ]
    }

    # Filter only the continuous range entries (those with a hyphen)
    continuous_entries = []
    for entry in previous_output['itinerary']:
        if '-' in entry['day_range']:
            continuous_entries.append(entry)
            
    # Parse the day range string into start and end integers
    def parse_range(day_range_str):
        parts = day_range_str.replace('Day ', '').split('-')
        start = int(parts[0])
        if len(parts) == 2:
            end = int(parts[1])
        else:
            end = start
        return start, end

    # Adjust the end day for each city except the last one
    adjusted_entries = []
    num_entries = len(continuous_entries)
    for idx, entry in enumerate(continuous_entries):
        start, end = parse_range(entry['day_range'])
        if idx < num_entries - 1:
            end = end - 1
        adjusted_entries.append({
            'place': entry['place'],
            'start': start,
            'end': end
        })
    
    # Format the adjusted entries
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
    
    # Output the corrected itinerary
    corrected = {
        'itinerary': result_itinerary
    }
    print(corrected)

if __name__ == "__main__":
    main()