# TLA⁺ model for Orange Meets Designated Committer Algorithm

This [PlusCal](https://learntla.com/core/index.html) specification describes the functionality of an end-to-end-encrypted Orange Meets room, using the Designated Committer joining method. In short, when a new user joins or leaves the room, the Designated Committer (the alive user with the lowest UID) is the one responsible for adding or removing them. All other users simply track who joins and leaves, in case they become the Designated Committer.

We describe the PlusCal data structures and processes below, as well as some lessons learned.

## Data structures

Every joining user is given a unique user ID (UID), which is a monotonically increasing counter.

`messages` is the global list of messages. This serves as the source of truth for ordering of events. In reality, this role is played by the MLS service provider (i.e., the Orange Meets app server). **All messages are sent via this broadcast channel, even ones meant for just 1 user.** There are three kinds of messages:

* `JoinLeaveType == [ty: {"user_left", "user_joined"}, uid: Nat]` — Indicates that the given `uid` joined or left the room.
* `MlsAddRemoveType == [ty: {"mls_add", "mls_remove"}, epoch: Nat, target_uid: Nat, sender: Nat ]` — Indicates that the UID `sender`, sent an MLS Add/Remove message, adding/removing `target_uid` at epoch `epoch`. These mesages signal to current members of the group that a user is being added/removed. The joiner does not process these.
* `MlsWelcomeType == [ty: {"mls_welcome"}, target_uid: Nat, epoch: Nat, sender: Nat]` — Indicates that the UID `sender` sent an MLS Welcome message, adding `target_uid` at epoch `epoch`. This message is intended for the user who just joined the group. Other members of the group do not process this (beyond recording that it happened).

`user_states` is the global list of all user states, indexed by their UID. Every entry in the list has the following fields:

* `welcomed: BOOLEAN` — Whether this user has gotten an MLS Welcome message yet
* `epoch: Nat` — The latest epoch of any message that this user has seen
* `idx_in_messages` — The index of the last message they read from the global `messages` list
* `users_pending_add` — The list of UIDs that have joined the group but not yet received an MLS Welcome and Add
* `users_pending_remove` — The list of UIDs that have left the group but not yet been removed via an MLS Remove

## Processes

Processes in PlusCal are algorithms that can run independently of each other, interleaving arbitrarily in time. Within processes are labels. Labels mark breakpoints where other things can happen. Everything that happens within one label is atomic. So for example, the Designated Committer must send two messages when a user joins, the Welcome and the Add. We have a separate label for these two steps, indicating that anything can occur between these two messages, including the death of the Designated Committer.

### Delivery Service

The `DeliveryService` process models the Orange Meets app server. It simply makes users join/leave the group. Joining implies appending a new user state to `user_states`, as well as a `user_joined` message to `messages`. Leaving implies appending a `user_left` message to `messages`. There is no distinction between a user leaving and a user dying, since in the latter case, the user will not respond to heartbeat pings, and thus be marked as "left" by the delivery service.

### Users

The `Users` process models every user, including the Designated Committer. Users don't have to do much. The first thing they do is wait for their own Welcome message. They need this to become active. After this, they only need to observe join/leave messages to append to their pendings list of users to add/remove, and observe add/remove messages to remove users from those pending lists.

### Designated Committer

The `DC` process models specifically the Designated Committer. Beyond the role of a normal user, the Designated Committer must also attempt to process its pending add/remove lists. For adds, it must send an MLS Welcome message to the joiner, followed by an Add message to the rest of the group. For removes, it must send an MLS Remove message to the rest of the group. The Designated Committer may leave at any time. When this happens, the alive user with the next lowest UID will take its place.

## Lessons learned

In the process of building this model, we learned all kinds of ways NOT to build a joining algorithm. The theme of these lessons was: order matters.

### Users should be welcomed in the order they arrive

When a user joins, the DC must send them a Welcome before any subsequent user joining. If we don't do this, we lose a helpful invariant: no two parties believe they're the DC at the same time.

Consider what happens otherwise. In this setup, we say the DC is the alive _added_ user with the lowest UID. Suppose UID 1 is the DC, and UIDs 2 and 3 join the group. 1 sends a Welcome to 3, then 2, and then dies. 3 sees just the first Welcome, and 2 sees both. Thus, 3 thinks they're the DC, and 2 thinks they're the DC.

### Welcomes must come before Adds

When a user joins, the Designated Committer cannot send an Add message before sending the corresponding Welcome message. Consider what happens when the order is flipped. The DC could send the Add message, then die. Then everyone has marked the joiner as added, but the joiner never received a Welcome, and thus cannot participate in the group.

Thus, the Welcome always comes first. If the DC dies after the Welcome, then the next DC will send another Welcome and an Add.

## License

This work is marked by Michael Rosenberg with [CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/).

## Disclaimer

This is not an officially supported Cloudflare product. This project is not eligible for the Cloudflare Vulnerability Rewards Program.
