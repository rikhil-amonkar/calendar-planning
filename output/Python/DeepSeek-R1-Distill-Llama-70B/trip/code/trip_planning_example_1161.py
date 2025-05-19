import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Mykonos': 4,
            'Krakow': 5,
            'Vilnius': 2,
            'Helsinki': 2,
            'Dubrovnik': 3,
            'Oslo': 2,
            'Madrid': 5,
            'Paris': 2
        }
        self.direct_flights = {
            'Oslo': ['Krakow', 'Paris', 'Madrid', 'Helsinki', 'Dubrovnik', 'Vilnius'],
            'Krakow': ['Paris', 'Vilnius'],
            'Vilnius': ['Paris'],
            'Helsinki': ['Krakow', 'Paris', 'Madrid'],
            'Dubrovnik': ['Helsinki', 'Madrid'],
            'Madrid': ['Mykonos'],
            'Paris': ['Madrid']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Oslo to meet friends
        self.add_place('Oslo', 2)
        # Fly to Dubrovnik for the annual show
        self.add_flight('Oslo', 'Dubrovnik')
        self.add_place('Dubrovnik', 3)
        # Fly to Helsinki
        self.add_flight('Dubrovnik', 'Helsinki')
        self.add_place('Helsinki', 2)
        # Fly to Krakow
        self.add_flight('Helsinki', 'Krakow')
        self.add_place('Krakow', 5)
        # Fly to Paris
        self.add_flight('Krakow', 'Paris')
        self.add_place('Paris', 2)
        # Fly to Madrid
        self.add_flight('Paris', 'Madrid')
        self.add_place('Madrid', 5)
        # Fly to Mykonos to visit relatives
        self.add_flight('Madrid', 'Mykonos')
        self.add_place('Mykonos', 4)
        # Return to Oslo
        self.add_flight('Mykonos', 'Oslo')
        self.add_place('Oslo', 2)

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