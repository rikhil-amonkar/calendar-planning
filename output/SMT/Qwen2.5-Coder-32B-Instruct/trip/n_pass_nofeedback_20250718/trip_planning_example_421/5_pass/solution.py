import json

# Manually construct the itinerary
itinerary = [
    {'day': 1, 'place': 'Nice'},
    {'day': 2, 'place': 'Nice'},
    {'day': 3, 'place': 'Nice'},
    {'day': 4, 'place': 'Nice'},
    {'day': 5, 'place': 'Nice'},
    {'day': 6, 'place': 'Dublin'},
    {'day': 7, 'place': 'Dublin'},
    {'day': 8, 'place': 'Dublin'},
    {'day': 9, 'place': 'Dublin'},
    {'day': 10, 'place': 'Dublin'},
    {'day': 11, 'place': 'Dublin'},
    {'day': 12, 'place': 'Dublin'},
    {'day': 13, 'place': 'Krakow'},
    {'day': 14, 'place': 'Krakow'},
    {'day': 15, 'place': 'Krakow'},
    {'day': 16, 'place': 'Krakow'},
    {'day': 17, 'place': 'Krakow'},
    {'day': 18, 'place': 'Krakow'},
    {'day': 19, 'place': 'Frankfurt'},
    {'day': 20, 'place': 'Frankfurt'}
]

# Output the itinerary in JSON format
print(json.dumps({'itinerary': itinerary}, indent=4))