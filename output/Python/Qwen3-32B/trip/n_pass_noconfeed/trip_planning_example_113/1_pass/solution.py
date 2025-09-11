import json

def main():
    days_required = {
        'Naples': 3,
        'Seville': 4,
        'Milan': 7
    }

    allowed_sequences = [
        ['Naples', 'Milan', 'Seville'],
        ['Seville', 'Milan', 'Naples']
    ]

    final_itinerary = None

    for sequence in allowed_sequences:
        current_start = 1
        itinerary = []
        seville_days = None
        for city in sequence:
            days = days_required[city]
            end = current_start + days - 1
            itinerary.append((current_start, end, city))
            if city == 'Seville':
                seville_days = (current_start, end)
            current_start = end
        if seville_days == (9, 12) and itinerary[-1][1] == 12:
            final_itinerary = itinerary
            break

    json_itinerary = []
    for start, end, place in final_itinerary:
        json_itinerary.append({
            'day_range': f"Day {start}-{end}",
            'place': place
        })

    result = {'itinerary': json_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()