import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Frankfurt': 4,
            'Salzburg': 5,
            'Athens': 5,
            'Reykjavik': 5,
            'Bucharest': 3,
            'Valencia': 2,
            'Vienna': 5,
            'Amsterdam': 3,
            'Stockholm': 3,
            'Riga': 3
        }
        self.direct_flights = {
            'Valencia': ['Frankfurt', 'Athens'],
            'Vienna': ['Bucharest', 'Riga', 'Frankfurt'],
            'Athens': ['Bucharest', 'Riga'],
            'Riga': ['Frankfurt', 'Bucharest'],
            'Frankfurt': ['Salzburg'],
            'Salzburg': [],
            'Amsterdam': ['Bucharest', 'Valencia', 'Riga'],
            'Stockholm': ['Vienna', 'Athens'],
            'Reykjavik': ['Athens']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Stockholm
        self.add_place('Stockholm', 3)
        # Fly to Vienna for the wedding
        self.add_flight('Stockholm', 'Vienna')
        self.add_place('Vienna', 5)
        # Fly to Valencia for the annual show
        self.add_flight('Vienna', 'Valencia')
        self.add_place('Valencia', 2)
        # Fly to Frankfurt
        self.add_flight('Valencia', 'Frankfurt')
        self.add_place('Frankfurt', 4)
        # Fly to Salzburg
        self.add_flight('Frankfurt', 'Salzburg')
        self.add_place('Salzburg', 5)
        # Fly to Athens for the workshop
        self.add_flight('Salzburg', 'Athens')
        self.add_place('Athens', 5)
        # Fly to Riga for the conference
        self.add_flight('Athens', 'Riga')
        self.add_place('Riga', 3)
        # Fly to Bucharest
        self.add_flight('Riga', 'Bucharest')
        self.add_place('Bucharest', 3)
        # Fly to Amsterdam
        self.add_flight('Bucharest', 'Amsterdam')
        self.add_place('Amsterdam', 3)
        # Fly to Reykjavik
        self.add_flight('Amsterdam', 'Reykjavik')
        self.add_place('Reykjavik', 5)

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