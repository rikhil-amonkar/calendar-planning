import json
from datetime import datetime, timedelta

def calculate_travel_time(distance, speed):
    # Assuming speed is in minutes per unit distance
    return distance * speed

def generate_itinerary(pacific_heights_arrival_time, jason_availability, kenneth_availability, travel_distances):
    # Convert arrival time to datetime object
    pacific_heights_arrival_time = datetime.strptime(pacific_heights_arrival_time, "%H:%M")
    
    # Initialize itinerary
    itinerary = []
    
    # Meet Jason
    jason_meeting_time = max(jason_availability[0], pacific_heights_arrival_time + timedelta(minutes=calculate_travel_time(travel_distances['Pacific Heights to Presidio'], 1)))
    jason_meeting_end_time = jason_meeting_time + timedelta(minutes=90)
    
    # Check if Jason is available for the entire meeting duration
    if jason_meeting_end_time <= jason_availability[1]:
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Jason",
            "start_time": jason_meeting_time.strftime("%H:%M"),
            "end_time": jason_meeting_end_time.strftime("%H:%M")
        })
    
    # Meet Kenneth
    kenneth_meeting_time = max(kenneth_availability[0], jason_meeting_end_time + timedelta(minutes=calculate_travel_time(travel_distances['Marina District to Pacific Heights'], 1)))
    kenneth_meeting_end_time = kenneth_meeting_time + timedelta(minutes=45)
    
    # Check if Kenneth is available for the entire meeting duration
    if kenneth_meeting_end_time <= kenneth_availability[1]:
        itinerary.append({
            "action": "meet",
            "location": "Marina District",
            "person": "Kenneth",
            "start_time": kenneth_meeting_time.strftime("%H:%M"),
            "end_time": kenneth_meeting_end_time.strftime("%H:%M")
        })
    
    return itinerary

def main():
    # Define travel distances
    travel_distances = {
        "Pacific Heights to Presidio": 11,
        "Pacific Heights to Marina District": 6,
        "Presidio to Pacific Heights": 11,
        "Presidio to Marina District": 10,
        "Marina District to Pacific Heights": 7,
        "Marina District to Presidio": 10
    }
    
    # Define meeting constraints
    pacific_heights_arrival_time = "09:00"
    jason_availability = [datetime.strptime("10:00", "%H:%M"), datetime.strptime("16:15", "%H:%M")]
    kenneth_availability = [datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:45", "%H:%M")]
    
    # Generate itinerary
    itinerary = generate_itinerary(pacific_heights_arrival_time, jason_availability, kenneth_availability, travel_distances)
    
    # Output itinerary as JSON
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()