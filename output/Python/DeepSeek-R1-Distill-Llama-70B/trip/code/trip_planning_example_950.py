import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Rome': 4,
            'Mykonos': 3,
            'Riga': 3,
            'Munich': 4,
            'Bucharest': 4,
            'Nice': 3,
            'Krakow': 2
        }
        self.direct_flights = {
            'Rome': ['Nice', 'Munich', 'Mykonos', 'Bucharest'],
            'Mykonos': ['Munich', 'Nice'],
            'Riga': ['Bucharest', 'Munich'],
            'Munich': ['Krakow', 'Nice', 'Riga'],
            'Bucharest': ['Munich', 'Riga'],
            'Nice': ['Munich', 'Riga'],
            'Krakow': []
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Rome for the conference
        self.add_place('Rome', 4)
        # Fly to Mykonos for the wedding
        self.add_flight('Rome', 'Mykonos')
        self.add_place('Mykonos', 3)
        # Fly to Munich
        self.add_flight('Mykonos', 'Munich')
        self.add_place('Munich', 4)
        # Fly to Nice
        self.add_flight('Munich', 'Nice')
        self.add_place('Nice', 3)
        # Fly to Bucharest
        self.add_flight('Nice', 'Bucharest')
        self.add_place('Bucharest', 4)
        # Fly to Riga
        self.add_flight('Bucharest', 'Riga')
        self.add_place('Riga', 3)
        # Fly to Krakow for the annual show
        self.add_flight('Riga', 'Krakow')
        self.add_place('Krakow', 2)

    def add_place(self, place, days):
        end_day = self.current_day + days - 1
        self.itinerary.append({'day_range': f'Day {self.current_day}-{end_day}', 'place': place})
        self.current_day = end_day + 1

    def add_flight(self, from_city, to_city):
        self.itinerary.append({'flying': f'Day {self.current_day}-{self.current_day}', 'from': from_city, 'to': to_city})
        self.current_day += 1

planner = TripPlanner()
planner.plan_trip()
print(json.dumps(planner.itinerary))