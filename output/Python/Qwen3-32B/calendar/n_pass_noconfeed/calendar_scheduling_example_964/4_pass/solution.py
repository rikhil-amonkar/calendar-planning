# Calendar Planning Script
from datetime import datetime, timedelta

def generate_calendar_events(start_date, num_days):
    """Generate sample calendar events for planning."""
    events = []
    current_date = start_date
    
    while len(events) < num_days:
        events.append({
            'date': current_date.strftime('%Y-%m-%d'),
            'event': f"Planning Session {len(events)+1}"
        })
        current_date += timedelta(days=1)
    
    return events

# Example usage
if __name__ == "__main__":
    start_date = datetime(2025, 9, 9)  # Example start date
    calendar = generate_calendar_events(start_date, 7)
    
    print("Generated Calendar Events:")
    for event in calendar:
        print(f"{event['date']}: {event['event']}")