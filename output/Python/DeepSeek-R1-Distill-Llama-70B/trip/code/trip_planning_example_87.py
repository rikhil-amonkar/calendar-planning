import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Riga': 2,
            'Amsterdam': 2,
            'Mykonos': 5
        }
        self.fixed_stays = {
            'Riga': (2, 1, 2)
        }
        self.flights = {
            'Riga': ['Amsterdam'],
            'Amsterdam': ['Mykonos'],
            'Mykonos': []
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Riga'  # Start with Riga as per the fixed stay

        # Riga stay
        riga_days = self.cities['Riga']
        itinerary.append({'day_range': f'Day 1-{riga_days}', 'place': 'Riga'})
        current_day += riga_days

        # Fly to Amsterdam
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Riga', 'to': 'Amsterdam'})
        current_day += 1

        # Amsterdam stay
        amsterdam_days = self.cities['Amsterdam']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + amsterdam_days - 1}', 'place': 'Amsterdam'})
        current_day += amsterdam_days

        # Fly to Mykonos
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Amsterdam', 'to': 'Mykonos'})
        current_day += 1

        # Mykonos stay
        mykonos_days = self.cities['Mykonos']
        # Adjust Mykonos stay to fit within the total 7 days
        mykonos_days = 7 - (current_day - 1)
        itinerary.append({'day_range': f'Day {current_day}-{current_day + mykonos_days - 1}', 'place': 'Mykonos'})

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