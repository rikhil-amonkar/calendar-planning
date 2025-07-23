itinerary_dict = {
    'itinerary': [
        {'day': 1, 'place': 'Valencia'},
        {'day': 2, 'place': 'Valencia'},
        {'day': 4, 'place': 'Riga'},
        {'day': 5, 'place': 'Riga'},
        {'day': 6, 'place': 'Riga'},
        {'day': 7, 'place': 'Riga'},
        {'day': 7, 'place': 'Brussels'},
        {'day': 8, 'place': 'Brussels'},
        {'day': 9, 'place': 'Brussels'},
        {'day': 10, 'place': 'Brussels'},
        {'day': 11, 'place': 'Brussels'},
        {'day': 11, 'place': 'Dubrovnik'},
        {'day': 12, 'place': 'Dubrovnik'},
        {'day': 13, 'place': 'Dubrovnik'},
        {'day': 16, 'place': 'Budapest'},
        {'day': 17, 'place': 'Budapest'},
        {'day': 6, 'place': 'Geneva'},
        {'day': 7, 'place': 'Geneva'},
        {'day': 8, 'place': 'Geneva'},
        {'day': 9, 'place': 'Geneva'},
        {'day': 10, 'place': 'Geneva'}
    ]
}

# Sort the itinerary by day
itinerary_dict['itinerary'].sort(key=lambda x: x['day'])

# Remove duplicate days by keeping the first occurrence of each day
unique_itinerary = []
seen_days = set()
for entry in itinerary_dict['itinerary']:
    if entry['day'] not in seen_days:
        unique_itinerary.append(entry)
        seen_days.add(entry['day'])

itinerary_dict['itinerary'] = unique_itinerary

print(itinerary_dict)