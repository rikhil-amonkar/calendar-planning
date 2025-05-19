import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Riga': 4,
            'Manchester': 5,
            'Bucharest': 4,
            'Florence': 4,
            'Vienna': 2,
            'Istanbul': 2,
            'Reykjavik': 4,
            'Stuttgart': 5
        }
        self.fixed_stays = {
            'Istanbul': (2, 12, 13),
            'Bucharest': (4, 16, 19)
        }
        self.flights = {
            'Bucharest': ['Vienna', 'Riga', 'Istanbul', 'Manchester'],
            'Reykjavik': ['Vienna'],
            'Manchester': ['Vienna', 'Riga', 'Bucharest', 'Istanbul', 'Stuttgart'],
            'Riga': ['Vienna', 'Bucharest', 'Istanbul', 'Manchester'],
            'Istanbul': ['Vienna', 'Riga', 'Bucharest', 'Stuttgart', 'Manchester'],
            'Vienna': ['Bucharest', 'Reykjavik', 'Manchester', 'Riga', 'Istanbul', 'Florence', 'Stuttgart'],
            'Florence': ['Vienna'],
            'Stuttgart': ['Vienna', 'Istanbul', 'Manchester'],
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Reykjavik'  # Starting point

        # Reykjavik stay
        days_in_reykjavik = self.cities['Reykjavik']
        itinerary.append({'day_range': f'Day 1-{days_in_reykjavik}', 'place': 'Reykjavik'})
        current_day += days_in_reykjavik

        # Fly to Vienna
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Vienna'})
        current_day += 1

        # Vienna stay
        days_in_vienna = self.cities['Vienna']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_vienna - 1}', 'place': 'Vienna'})
        current_day += days_in_vienna

        # Fly to Florence
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Florence'})
        current_day += 1

        # Florence stay
        days_in_florence = self.cities['Florence']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_florence - 1}', 'place': 'Florence'})
        current_day += days_in_florence

        # Fly back to Vienna
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Florence', 'to': 'Vienna'})
        current_day += 1

        # Vienna stay (1 day this time)
        days_in_vienna = 1
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_vienna - 1}', 'place': 'Vienna'})
        current_day += days_in_vienna

        # Fly to Istanbul
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Istanbul'})
        current_day += 1

        # Istanbul stay
        days_in_istanbul = self.cities['Istanbul']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_istanbul - 1}', 'place': 'Istanbul'})
        current_day += days_in_istanbul

        # Fly to Vienna
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Istanbul', 'to': 'Vienna'})
        current_day += 1

        # Vienna stay
        days_in_vienna = self.cities['Vienna']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_vienna - 1}', 'place': 'Vienna'})
        current_day += days_in_vienna

        # Fly to Bucharest
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Bucharest'})
        current_day += 1

        # Bucharest stay
        days_in_bucharest = self.cities['Bucharest']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_bucharest - 1}', 'place': 'Bucharest'})
        current_day += days_in_bucharest

        # Fly to Riga
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Riga'})
        current_day += 1

        # Riga stay
        days_in_riga = self.cities['Riga']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_in_riga - 1}', 'place': 'Riga'})
        current_day += days_in_riga

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