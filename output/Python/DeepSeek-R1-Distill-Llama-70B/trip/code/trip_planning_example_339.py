import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Warsaw': 2,
            'Budapest': 7,
            'Paris': 4,
            'Riga': 7
        }
        self.fixed_stays = {
            'Warsaw': (2, 1, 2),
            'Riga': (7, 11, 17)
        }
        self.flights = {
            'Warsaw': ['Budapest', 'Paris'],
            'Budapest': ['Paris'],
            'Paris': ['Riga'],
            'Riga': []
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Warsaw'  # Start with Warsaw to attend the annual show

        # Warsaw stay
        warsaw_days = self.cities['Warsaw']
        itinerary.append({'day_range': f'Day 1-{warsaw_days}', 'place': 'Warsaw'})
        current_day += warsaw_days

        # Fly to Budapest
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Warsaw', 'to': 'Budapest'})
        current_day += 1

        # Budapest stay
        budapest_days = self.cities['Budapest']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + budapest_days - 1}', 'place': 'Budapest'})
        current_day += budapest_days

        # Fly to Paris
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Budapest', 'to': 'Paris'})
        current_day += 1

        # Paris stay
        paris_days = self.cities['Paris']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + paris_days - 1}', 'place': 'Paris'})
        current_day += paris_days

        # Fly to Riga
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Paris', 'to': 'Riga'})
        current_day += 1

        # Riga stay
        riga_days = self.cities['Riga']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + riga_days - 1}', 'place': 'Riga'})
        current_day += riga_days

        return itinerary

planner = TripPlanner()
itinerary = planner.compute_itinerary()

# Adjusting the day ranges to match the required format
for item in itinerary:
    if 'day_range' in item:
        days = item['day_range'].split('-')
        start_day = days[1]
        end_day = days[2] if len(days) > 2 else start_day
        item['day_range'] = f'Day {start_day}-{end_day}'
    elif 'flying' in item:
        flying_day = item['flying'].split('-')[1]
        item['flying'] = f'Day {flying_day}'

print(json.dumps(itinerary, indent=2))