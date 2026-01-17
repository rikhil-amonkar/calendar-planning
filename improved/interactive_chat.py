#!/usr/bin/env python3
"""
Interactive chat interface for discussing Natural Plan problems with LLMs.
Provides a command-line interface for smooth conversations.
"""

import sys
from typing import Optional
from conversation_manager import ConversationManager
from dataset_loader import NaturalPlanDataset, TaskType


class InteractiveChat:
    """Interactive chat interface for Natural Plan problems."""
    
    def __init__(self, model: str = "gpt-3.5-turbo"):
        """Initialize the interactive chat."""
        self.manager = ConversationManager(model=model)
        self.dataset = NaturalPlanDataset()
        self.running = False
    
    def print_help(self):
        """Print help information."""
        print("\n" + "="*70)
        print("COMMANDS:")
        print("="*70)
        print("  /new <task> <index>  - Start new conversation (e.g., /new calendar 0)")
        print("  /random <task>       - Start with random problem (e.g., /random meeting)")
        print("  /solution            - Show golden solution for current problem")
        print("  /history             - Display full conversation history")
        print("  /save [filename]     - Save conversation to file")
        print("  /load <filename>     - Load a saved conversation")
        print("  /list                - List available tasks and counts")
        print("  /model               - Show current model being used")
        print("  /help                - Show this help message")
        print("  /quit or /exit       - Exit the chat")
        print("\nTo chat with the LLM, just type your message and press Enter.")
        print("="*70 + "\n")
    
    def print_welcome(self):
        """Print welcome message."""
        print("\n" + "="*70)
        print("  NATURAL PLAN CONVERSATION INTERFACE")
        print("="*70)
        print(f"\nModel: {self.manager.model}")
        print("\nWelcome! This interface helps you discuss Natural Plan problems with LLMs.")
        print("Type /help to see available commands.")
        print("Type /new <task> <index> to start a conversation (e.g., /new calendar 0)")
        print("Type /model to see model information.")
        print("="*70 + "\n")
    
    def list_tasks(self):
        """List available tasks."""
        print("\n" + "="*70)
        print("AVAILABLE TASKS:")
        print("="*70)
        tasks = self.dataset.list_available_tasks()
        for task_type, splits in tasks.items():
            print(f"\n{task_type.upper()}:")
            for split, count in splits.items():
                print(f"  {split}: {count} problems")
        print("="*70 + "\n")
    
    def show_model_info(self):
        """Show current model information."""
        print("\n" + "="*70)
        print("MODEL INFORMATION:")
        print("="*70)
        print(f"  Current model: {self.manager.model}")
        print(f"\n  To use a different model, restart with:")
        print(f"    python interactive_chat.py <model_name>")
        print(f"\n  Available models (December 2025):")
        print(f"    OpenAI:")
        print(f"      - gpt-3.5-turbo (fast, cheaper)")
        print(f"      - gpt-4 (capable)")
        print(f"      - gpt-4-turbo (fast GPT-4)")
        print(f"      - gpt-4o, gpt-4o-mini (multimodal)")
        print(f"      - gpt-5 (latest, released Aug 2025)")
        print(f"      - gpt-5.2 (enhanced GPT-5)")
        print(f"      - o1, o1-mini, o3, o3-mini (reasoning)")
        print(f"    Deepseek:")
        print(f"      - deepseek-v3 (flagship model)")
        print(f"      - deepseek-reasoner (reasoning model)")
        print("="*70 + "\n")
    
    def start_new_conversation(self, task_type: str, index: int, shot_type: str = "0shot"):
        """Start a new conversation."""
        try:
            problem_text = self.manager.start_conversation(
                task_type=task_type,
                problem_index=index,
                shot_type=shot_type
            )
            
            print("\n" + "="*70)
            print(f"NEW CONVERSATION - {task_type.upper()} Problem #{index}")
            print("="*70)
            print("\nPROBLEM:")
            print(problem_text)
            print("\n" + "="*70)
            print("You can now chat with the LLM about this problem.")
            print("Type /solution to see the golden solution.")
            print("="*70 + "\n")
            
        except Exception as e:
            print(f"\nError starting conversation: {e}\n")
    
    def start_random_conversation(self, task_type: str, shot_type: str = "0shot"):
        """Start a conversation with a random problem."""
        try:
            problem = self.dataset.get_random_problem(task_type)
            
            # Find the index
            data = self.dataset.load_task_data(task_type)
            index = next(i for i, p in enumerate(data) if p["id"] == problem["id"])
            
            self.start_new_conversation(task_type, index, shot_type)
            
        except Exception as e:
            print(f"\nError starting random conversation: {e}\n")
    
    def show_solution(self):
        """Show the golden solution."""
        try:
            solution = self.manager.get_golden_solution()
            print("\n" + "="*70)
            print("GOLDEN SOLUTION:")
            print("="*70)
            print(solution)
            print("="*70 + "\n")
        except Exception as e:
            print(f"\nError: {e}\n")
    
    def save_conversation(self, filename: Optional[str] = None):
        """Save the current conversation."""
        try:
            filepath = self.manager.save_conversation(filename)
            print(f"\nConversation saved to: {filepath}\n")
        except Exception as e:
            print(f"\nError saving conversation: {e}\n")
    
    def load_conversation(self, filename: str):
        """Load a saved conversation."""
        try:
            self.manager.load_conversation(filename)
            print(f"\nConversation loaded from: {filename}")
            self.manager.display_conversation()
        except Exception as e:
            print(f"\nError loading conversation: {e}\n")
    
    def handle_command(self, command: str) -> bool:
        """
        Handle a command.
        
        Returns:
            True to continue, False to exit
        """
        parts = command.strip().split()
        cmd = parts[0].lower()
        
        if cmd in ["/quit", "/exit"]:
            return False
        
        elif cmd == "/help":
            self.print_help()
        
        elif cmd == "/list":
            self.list_tasks()
        
        elif cmd == "/model":
            self.show_model_info()
        
        elif cmd == "/new":
            if len(parts) < 3:
                print("\nUsage: /new <task_type> <index> [shot_type]")
                print("Example: /new calendar 0 0shot\n")
            else:
                task_type = parts[1]
                try:
                    index = int(parts[2])
                    shot_type = parts[3] if len(parts) > 3 else "0shot"
                    self.start_new_conversation(task_type, index, shot_type)
                except ValueError:
                    print("\nError: Index must be a number\n")
        
        elif cmd == "/random":
            if len(parts) < 2:
                print("\nUsage: /random <task_type> [shot_type]")
                print("Example: /random meeting 0shot\n")
            else:
                task_type = parts[1]
                shot_type = parts[2] if len(parts) > 2 else "0shot"
                self.start_random_conversation(task_type, shot_type)
        
        elif cmd == "/solution":
            self.show_solution()
        
        elif cmd == "/history":
            self.manager.display_conversation()
        
        elif cmd == "/save":
            filename = parts[1] if len(parts) > 1 else None
            self.save_conversation(filename)
        
        elif cmd == "/load":
            if len(parts) < 2:
                print("\nUsage: /load <filename>\n")
            else:
                self.load_conversation(parts[1])
        
        else:
            print(f"\nUnknown command: {cmd}")
            print("Type /help to see available commands.\n")
        
        return True
    
    def run(self):
        """Run the interactive chat loop."""
        self.running = True
        self.print_welcome()
        
        while self.running:
            try:
                user_input = input("You: ").strip()
                
                if not user_input:
                    continue
                
                # Handle commands
                if user_input.startswith("/"):
                    self.running = self.handle_command(user_input)
                    continue
                
                # Send message to LLM
                if not self.manager.current_problem:
                    print("\nNo active conversation. Use /new or /random to start one.\n")
                    continue
                
                print("\nThinking...\n")
                response = self.manager.send_message(user_input)
                print(f"Assistant: {response}\n")
                
            except KeyboardInterrupt:
                print("\n\nInterrupted. Type /quit to exit or continue chatting.\n")
            except EOFError:
                break
            except Exception as e:
                print(f"\nError: {e}\n")
        
        print("\nGoodbye!\n")


def main():
    """Main entry point."""
    # Parse command line arguments
    model = "gpt-3.5-turbo"
    
    # List of known valid models (as of December 2025)
    valid_models = [
        "gpt-3.5-turbo", "gpt-3.5-turbo-16k",
        "gpt-4", "gpt-4-turbo", "gpt-4-turbo-preview",
        "gpt-4-1106-preview", "gpt-4o", "gpt-4o-mini",
        "gpt-5", "gpt-5.2", "gpt-5.2-codex",  # GPT-5 series (released Aug 2025)
        "o1-preview", "o1-mini"
    ]
    
    if len(sys.argv) > 1:
        if sys.argv[1] in ["-h", "--help"]:
            print("Usage: python interactive_chat.py [model_name]")
            print("\nExample:")
            print("  python interactive_chat.py gpt-4")
            print("  python interactive_chat.py gpt-3.5-turbo")
            print("\nCommon models:")
            for m in valid_models[:6]:  # Show first 6
                print(f"  - {m}")
            sys.exit(0)
        else:
            model = sys.argv[1]
            
            # Warn if model doesn't look valid
            if model not in valid_models and not model.startswith("gpt-"):
                print(f"\n⚠ Warning: '{model}' may not be a valid model.")
                print(f"Valid models include: {', '.join(valid_models[:4])}")
                response = input("Continue anyway? (y/n): ")
                if response.lower() != 'y':
                    sys.exit(0)
    
    chat = InteractiveChat(model=model)
    chat.run()


if __name__ == "__main__":
    main()

