import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Mykonos': 2,
            'Vienna': 4,
            'Venice': 6
        }
        self.fixed_stays = {
            'Venice': (6, 5, 10)
        }
        self.flights = {
            'Mykonos': ['Vienna'],
            'Vienna': ['Venice'],
            'Venice': []
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Mykonos'  # Start with Mykonos

        # Mykonos stay
        mykonos_days = self.cities['Mykonos']
        itinerary.append({'day_range': f'Day 1-{mykonos_days}', 'place': 'Mykonos'})
        current_day += mykonos_days

        # Fly to Vienna
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Mykonos', 'to': 'Vienna'})
        current_day += 1

        # Vienna stay
        vienna_days = self.cities['Vienna']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + vienna_days - 1}', 'place': 'Vienna'})
        current_day += vienna_days

        # Fly to Venice
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Venice'})
        current_day += 1

        # Venice stay
        venice_days = self.cities['Venice']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + venice_days - 1}', 'place': 'Venice'})
        current_day += venice_days

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